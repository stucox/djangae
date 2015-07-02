#STANDARD LIB
from datetime import datetime
import logging
import copy
import re
from functools import partial
from itertools import chain, groupby

#LIBRARIES
from django.db import DatabaseError
from django.core.exceptions import FieldError
from django.db.models.fields import FieldDoesNotExist

from django.core.cache import cache
from django.db import IntegrityError
from django.db.models.sql.datastructures import EmptyResultSet
from django.db.models.sql import query
from django.db.models.sql.where import EmptyWhere
from django.db.models.fields import AutoField
from google.appengine.api import datastore, datastore_errors
from google.appengine.api.datastore import Query
from google.appengine.ext import db

#DJANGAE
from djangae.db.backends.appengine.dbapi import CouldBeSupportedError, NotSupportedError
from djangae.db.utils import (
    get_datastore_key,
    django_instance_to_entity,
    get_prepared_db_value,
    MockInstance,
    get_top_concrete_parent,
    get_concrete_parents,
    has_concrete_parents
)
from djangae.indexing import special_indexes_for_column, REQUIRES_SPECIAL_INDEXES, add_special_index
from djangae.utils import on_production, memoized
from djangae.db import constraints, utils
from djangae.db.backends.appengine import caching
from djangae.db.unique_utils import query_is_unique
from djangae.db.backends.appengine import transforms
from djangae.db.caching import clear_context_cache

DATE_TRANSFORMS = {
    "year": transforms.year_transform,
    "month": transforms.month_transform,
    "day": transforms.day_transform,
    "hour": transforms.hour_transform,
    "minute": transforms.minute_transform,
    "second": transforms.second_transform
}

DJANGAE_LOG = logging.getLogger("djangae")

OPERATORS_MAP = {
    'exact': '=',
    'gt': '>',
    'gte': '>=',
    'lt': '<',
    'lte': '<=',

    # The following operators are supported with special code below.
    'isnull': None,
    'in': None,
    'range': None,
}

EXTRA_SELECT_FUNCTIONS = {
    '+': lambda x, y: x + y,
    '-': lambda x, y: x - y,
    '/': lambda x, y: x / y,
    '*': lambda x, y: x * y,
    '<': lambda x, y: x < y,
    '>': lambda x, y: x > y,
    '=': lambda x, y: x == y
}

REVERSE_OP_MAP = {
    '=':'exact',
    '>':'gt',
    '>=':'gte',
    '<':'lt',
    '<=':'lte',
}

INEQUALITY_OPERATORS = frozenset(['>', '<', '<=', '>='])

def _cols_from_where_node(where_node):
    cols = where_node.get_cols() if hasattr(where_node, 'get_cols') else where_node.get_group_by_cols()
    return cols

def _get_tables_from_where(where_node):
    cols = _cols_from_where_node(where_node)
    return list(set([x[0] for x in cols if x[0] ]))

@memoized
def get_field_from_column(model, column):
    for field in model._meta.fields:
        if field.column == column:
            return field
    return None


def field_conv_year_only(value):
    value = ensure_datetime(value)
    return datetime(value.year, 1, 1, 0, 0)


def field_conv_month_only(value):
    value = ensure_datetime(value)
    return datetime(value.year, value.month, 1, 0, 0)


def field_conv_day_only(value):
    value = ensure_datetime(value)
    return datetime(value.year, value.month, value.day, 0, 0)


def ensure_datetime(value):
    """
        Painfully, sometimes the Datastore returns dates as datetime objects, and sometimes
        it returns them as unix timestamps in microseconds!!
    """
    if isinstance(value, long):
        return datetime.fromtimestamp(value / 1000000)
    return value

def coerce_unicode(value):
    if isinstance(value, str):
        try:
            value = value.decode('utf-8')
        except UnicodeDecodeError:
            # This must be a Django databaseerror, because the exception happens too
            # early before Django's exception wrapping can take effect (e.g. it happens on SQL
            # construction, not on execution.
            raise DatabaseError("Bytestring is not encoded in utf-8")

    # The SDK raises BadValueError for unicode sub-classes like SafeText.
    return unicode(value)


FILTER_CMP_FUNCTION_MAP = {
    'exact': lambda a, b: a == b,
    'iexact': lambda a, b: a.lower() == b.lower(),
    'gt': lambda a, b: a > b,
    'lt': lambda a, b: a < b,
    'gte': lambda a, b: a >= b,
    'lte': lambda a, b: a <= b,
    'isnull': lambda a, b: (b and (a is None)) or (a is not None),
    'in': lambda a, b: a in b,
    'startswith': lambda a, b: a.startswith(b),
    'range': lambda a, b: b[0] < a < b[1], #I'm assuming that b is a tuple
    'year': lambda a, b: field_conv_year_only(a) == b,
}


def log_once(logging_call, text, args):
    """
        Only logs one instance of the combination of text and arguments to the passed
        logging function
    """
    identifier = "%s:%s" % (text, args)
    if identifier in log_once.logged:
        return
    logging_call(text % args)
    log_once.logged.add(identifier)

log_once.logged = set()


def parse_constraint(child, connection, negated=False):
    if isinstance(child, tuple):
        # First, unpack the constraint
        constraint, op, annotation, value = child
        was_list = isinstance(value, (list, tuple))
        if isinstance(value, query.Query):
            value = value.get_compiler(connection.alias).as_sql()[0].execute()
        else:
            packed, value = constraint.process(op, value, connection)
        alias, column, db_type = packed
        field = constraint.field
    else:
        # Django 1.7+
        field = child.lhs.target
        column = child.lhs.target.column
        op = child.lookup_name
        value = child.rhs
        annotation = value
        was_list = isinstance(value, (list, tuple))

        if isinstance(value, query.Query):
            value = value.get_compiler(connection.alias).as_sql()[0].execute()
        elif value != []:
            value = child.lhs.output_field.get_db_prep_lookup(
                child.lookup_name, child.rhs, connection, prepared=True)


    is_pk = field and field.primary_key

    if column == "id" and op == "iexact" and is_pk and isinstance(field, AutoField):
        # When new instance is created, automatic primary key 'id' does not generate '_idx_iexact_id'.
        # As the primary key 'id' (AutoField) is integer and is always case insensitive, we can deal with 'id_iexact=' query by using 'exact' rather than 'iexact'.
        op = "exact"

    if field and field.db_type(connection) in ("bytes", "text"):
        raise NotSupportedError("Text and Blob fields are not indexed by the datastore, so you can't filter on them")

    if op not in REQUIRES_SPECIAL_INDEXES:
        # Don't convert if this op requires special indexes, it will be handled there
        if field:
            value = [ connection.ops.prep_lookup_value(field.model, x, field, column=column) for x in value]

        # Don't ask me why, but on Django 1.6 constraint.process on isnull wipes out the value (it returns an empty list)
        # so we have to special case this to use the annotation value instead
        if op == "isnull":
            if annotation is not None:
                value = [ annotation ]

            if is_pk and value[0]:
                raise EmptyResultSet()

        if not was_list:
            value = value[0]
    else:
        if negated:
            raise CouldBeSupportedError("Special indexing does not currently supported negated queries. See #80")

        if not was_list:
            value = value[0]

        add_special_index(field.model, column, op)  # Add the index if we can (e.g. on dev_appserver)

        if op not in special_indexes_for_column(field.model, column):
            raise RuntimeError("There is a missing index in your djangaeidx.yaml - \n\n{0}:\n\t{1}: [{2}]".format(
                field.model, column, op)
            )

        indexer = REQUIRES_SPECIAL_INDEXES[op]
        value = indexer.prep_value_for_query(value)
        column = indexer.indexed_column_name(column, value=value)
        op = indexer.prep_query_operator(op)

    return column, op, value


def convert_keys_to_entities(results):
    """
        If for performance reasons we do a keys_only query, then the result
        of the query will be a list of keys, not a list of entities. Here
        we convert to a FakeEntity type which should be enough for the rest of the
        pipeline to process without knowing any different!
    """

    class FakeEntity(dict):
        def __init__(self, key):
            self._key = key

        def key(self):
            return self._key

    for result in results:
        if isinstance(result, datastore.Key):
            yield FakeEntity(result)
        else:
            yield FakeEntity(result.key())


def _convert_entity_based_on_query_options(entity, opts):
    if opts.keys_only:
        return entity.key()

    if opts.projection:
        for k in entity.keys()[:]:
            if k not in list(opts.projection) + ["class"]:
                del entity[k]

    return entity


def _get_key(query):
    return query["__key__ ="]

class QueryByKeys(object):
    def __init__(self, model, queries, ordering):
        self.model = model
        self.queries = queries
        self.queries_by_key = { a: list(b) for a, b in groupby(queries, lambda x: _get_key(x)) }
        self.ordering = ordering
        self._Query__kind = queries[0]._Query__kind

    def Run(self, limit=None, offset=None):
        assert not self.queries[0]._Query__ancestor_pb #FIXME: We don't handle this yet

        # FIXME: What if the query options differ?
        opts = self.queries[0]._Query__query_options

        results = None

        # If we have a single key lookup going on, just hit the cache
        if len(self.queries_by_key) == 1:
            keys = self.queries_by_key.keys()
            ret = caching.get_from_cache_by_key(keys[0])
            if ret is not None:
                results = [ret]

        # If there was nothing in the cache, or we had more than one key, then use Get()
        if results is None:
            keys = self.queries_by_key.keys()
            results = datastore.Get(keys)
            for result in results:
                if result is None:
                    continue
                caching.add_entity_to_cache(self.model, result, caching.CachingSituation.DATASTORE_GET)
            results = sorted((x for x in results if x is not None), cmp=partial(utils.django_ordering_comparison, self.ordering))

        results = [
            _convert_entity_based_on_query_options(x, opts)
            for x in results if any([ utils.entity_matches_query(x, qry) for qry in self.queries_by_key[x.key()]])
        ]

        if offset:
            results = results[offset:]

        if limit is not None:
            results = results[:limit]

        return iter(results)

    def Count(self, limit, offset):
        return len([ x for x in self.Run(limit, offset) ])


class NoOpQuery(object):
    def Run(self, limit, offset):
        return []

    def Count(self, limit, offset):
        return 0


class UniqueQuery(object):
    """
        This mimics a normal query but hits the cache if possible. It must
        be passed the set of unique fields that form a unique constraint
    """
    def __init__(self, unique_identifier, gae_query, model):
        self._identifier = unique_identifier
        self._gae_query = gae_query
        self._model = model

    def Run(self, limit, offset):
        opts = self._gae_query._Query__query_options
        if opts.keys_only or opts.projection:
            return self._gae_query.Run(limit=limit, offset=offset)

        ret = caching.get_from_cache(self._identifier)
        if ret is not None and not utils.entity_matches_query(ret, self._gae_query):
            ret = None

        if ret is None:
            # We do a fast keys_only query to get the result
            keys_query = Query(self._gae_query._Query__kind, keys_only=True)
            keys_query.update(self._gae_query)
            keys = keys_query.Run(limit=limit, offset=offset)

            # Do a consistent get so we don't cache stale data, and recheck the result matches the query
            ret = [ x for x in datastore.Get(keys) if utils.entity_matches_query(x, self._gae_query) ]
            if len(ret) == 1:
                caching.add_entity_to_cache(self._model, ret[0], caching.CachingSituation.DATASTORE_GET)
            return iter(ret)

        return iter([ ret ])

    def Count(self, limit, offset):
        ret = caching.get_from_cache(self._identifier)
        if ret is not None and not utils.entity_matches_query(ret, self._gae_query):
            ret = None

        if ret is None:
            return self._gae_query.Count(limit=limit, offset=offset)
        return 1

def _convert_ordering(query):
    if not query.default_ordering:
        result = query.order_by
    else:
        result = query.order_by or query.get_meta().ordering

    if query.extra_order_by:
        # This is a best attempt at ordering by extra select, it covers the cases
        # in the Django tests, but use this functionality with care
        all_fields = query.get_meta().get_all_field_names()
        new_ordering = []
        for col in query.extra_order_by:
            # If the query in the extra order by is part of the extra select
            # and the extra select is just an alias, then use the original column
            if col in query.extra_select:
                if query.extra_select[col][0] in all_fields:
                    new_ordering.append(query.extra_select[col][0])
                else:
                    # It wasn't an alias, probably can't support it
                    raise NotSupportedError("Unsupported extra_order_by: {}".format(query.extra_order_by))
            else:
                # Not in the extra select, probably just a column so use it if it is
                if col in all_fields:
                    new_ordering.append(col)
                else:
                    raise NotSupportedError("Unsupported extra_order_by: {}".format(query.extra_order_by))

        result = tuple(new_ordering)

    if result:
        # We factor out cross-table orderings (rather than raising NotSupportedError) otherwise we'll break
        # the admin which uses them. We log a warning when this happens though
        try:
            ordering = []
            for name in result:
                if name == "?":
                    raise NotSupportedError("Random ordering is not supported on the datastore")

                if not (isinstance(name, basestring) and "__" in name):
                    if isinstance(name, basestring):
                        if name.lstrip("-") == "pk":
                            field_column = query.model._meta.pk.column
                        else:
                            field = query.model._meta.get_field_by_name(name.lstrip("-"))[0]
                            field_column = field.column
                        ordering.append(field_column if not name.startswith("-") else "-{}".format(field_column))
                    else:
                        ordering.append(name)

        except FieldDoesNotExist:
            opts = query.model._meta
            available = opts.get_all_field_names()
            raise FieldError("Cannot resolve keyword %r into field. "
                "Choices are: %s" % (name, ", ".join(available))
            )

        if len(ordering) < len(result):
            diff = set(result) - set(ordering)
            log_once(
                DJANGAE_LOG.warning if not on_production() else DJANGAE_LOG.debug,
                "The following orderings were ignored as cross-table orderings are not supported on the datastore: %s", diff
            )
        result = ordering


    return result

def _apply_extra_to_entity(extra_select, entity, pk_col):
    """
        Obviously the datastore doesn't support extra columns, but we can emulate simple
        extra selects as we iterate the results. This function does that!
    """

    def prep_value(attr):
        if attr == pk_col:
            attr = entity.key().id_or_name()
        else:
            attr = entity[attr] if attr in entity else attr

        try:
            attr = int(attr)
        except (TypeError, ValueError):
            pass

        if isinstance(attr, basestring):
            if (attr[0], attr[-1]) == ("'", "'"):
                attr = attr[1:-1]
            elif (attr[0], attr[-1]) == ('"', '"'):
                attr = attr[1:-1]
        return attr

    for column, (select, _) in extra_select.iteritems():

        arithmetic_regex = "(\w+)\s?([+|-|/|*|\=])\s?([\w|'|\"]+)"
        match = re.match(arithmetic_regex, select)
        if match:
            lhs = match.group(1)
            op = match.group(2)
            rhs = match.group(3)

            lhs = prep_value(lhs)
            rhs = prep_value(rhs)

            fun = EXTRA_SELECT_FUNCTIONS.get(op)
            if not fun:
                raise NotSupportedError("Unimplemented extra select operation: '%s'" % op)

            entity[column] = fun(lhs, rhs)
        else:
            rhs = prep_value(select)
            entity[column] = rhs

    return entity

class SelectCommand(object):
    def __init__(self, connection, query, keys_only=False):
        self.where = None

        self.original_query = query
        self.connection = connection

        self.limits = (query.low_mark, query.high_mark)
        self.results_returned = 0

        opts = query.get_meta()

        self.distinct = query.distinct
        self.distinct_values = set()
        self.distinct_on_field = None
        self.distinct_field_convertor = None
        self.queried_fields = []
        self.model = query.model
        self.pk_col = opts.pk.column
        self.is_count = query.aggregates
        self.extra_select = query.extra_select
        self._set_db_table()

        try:
            self._validate_query_is_possible(query)
            self.ordering = _convert_ordering(query)
        except NotSupportedError as e:
            # If we can detect here, or when parsing the WHERE tree that a query is unsupported
            # we set this flag, and then throw NotSupportedError when execute is called.
            # This will then wrap the exception in Django's NotSupportedError meaning users
            # only need to catch that one, and not both Django's and ours
            self.unsupported_query_message = str(e)
            return
        else:
            self.unsupported_query_message = ""


        # If the query uses defer()/only() then we need to process deferred. We have to get all deferred columns
        # for all (concrete) inherited models and then only include columns if they appear in that list
        deferred_columns = {}
        query.deferred_to_data(deferred_columns, query.deferred_to_columns_cb)
        inherited_db_tables = [x._meta.db_table for x in get_concrete_parents(self.model)]
        only_load = list(chain(*[list(deferred_columns.get(x, [])) for x in inherited_db_tables]))

        if query.select:
            for x in query.select:
                if hasattr(x, "field"):
                    # In Django 1.6+ 'x' above is a SelectInfo (which is a tuple subclass), whereas in 1.5 it's a tuple
                    # in 1.6 x[1] == Field, but 1.5 x[1] == unicode (column name)
                    if x.field is None:
                        column = x.col.col[1]  # This is the column we are getting
                        lookup_type = x.col.lookup_type

                        self.distinct_on_field = column

                        # This whole section of code is weird, and is probably better implemented as a custom Query type (like QueryByKeys)
                        # basically, appengine gives back dates as a time since the epoch, we convert it to a date, then floor it, then convert it back
                        # in our transform function. The transform is applied when the results are read back so that only distinct values are returned.
                        # this is very hacky...
                        if lookup_type in DATE_TRANSFORMS:
                            self.distinct_field_convertor = lambda value: DATE_TRANSFORMS[lookup_type](self.connection, value)
                        else:
                            raise CouldBeSupportedError("Unhandled lookup_type %s" % lookup_type)
                    else:
                        column = x.field.column
                else:
                    column = x[1]

                if only_load and column not in only_load:
                    continue

                self.queried_fields.append(column)
        else:
            # If no specific fields were specified, select all fields if the query is distinct (as App Engine only supports
            # distinct on projection queries) or the ones specified by only_load
            self.queried_fields = [x.column for x in opts.fields if (x.column in only_load) or self.distinct]

        self.keys_only = keys_only or self.queried_fields == [opts.pk.column]

        # Projection queries don't return results unless all projected fields are
        # indexed on the model. This means if you add a field, and all fields on the model
        # are projectable, you will never get any results until you've resaved all of them.

        # Because it's not possible to detect this situation, we only try a projection query if a
        # subset of fields was specified (e.g. values_list('bananas')) which makes the behaviour a
        # bit more predictable. It would be nice at some point to add some kind of force_projection()
        # thing on a queryset that would do this whenever possible, but that's for the future, maybe.
        try_projection = (self.keys_only is False) and bool(self.queried_fields)

        if not self.queried_fields:
            # If we don't have any queried fields yet, it must have been an empty select and not a distinct
            # and not an only/defer, so get all the fields
            self.queried_fields = [ x.column for x in opts.fields ]

        self.excluded_pks = set()

        self.has_inequality_filter = False
        self.all_filters = []
        self.results = None

        self.gae_query = None

        projection_fields = []

        if try_projection:
            for field in self.queried_fields:
                # We don't include the primary key in projection queries...
                if field == self.pk_col:
                    order_fields = set([ x.strip("-") for x in self.ordering])

                    if self.pk_col in order_fields or "pk" in order_fields:
                        # If we were ordering on __key__ we can't do a projection at all
                        self.projection_fields = []
                        break
                    continue

                # Text and byte fields aren't indexed, so we can't do a
                # projection query
                f = get_field_from_column(self.model, field)
                if not f:
                    raise CouldBeSupportedError("Attempting a cross-table select or dates query, or something?!")
                assert f  # If this happens, we have a cross-table select going on! #FIXME
                db_type = f.db_type(connection)

                if db_type in ("bytes", "text", "list", "set"):
                    projection_fields = []
                    break

                projection_fields.append(field)

        self.projection = list(set(projection_fields)) or None
        if opts.parents:
            self.projection = None

        if isinstance(query.where, EmptyWhere):
            # Empty where means return nothing!
            raise EmptyResultSet()
        else:
            try:
                where_tables = _get_tables_from_where(query.where)
            except TypeError:
                # This exception is thrown by get_group_by_cols if one of the constraints is a SubQueryConstraint
                # yeah, we can't do that.
                self.unsupported_query_message = "Subquery WHERE constraints aren't supported"
                return

            if where_tables and where_tables != [ query.model._meta.db_table ]:
                # Mark this query as unsupported and return
                self.unsupported_query_message = "Cross-join WHERE constraints aren't supported: %s" % _cols_from_where_node(query.where)
                return

            from dnf import parse_dnf
            try:
                self.where, columns, self.excluded_pks = parse_dnf(query.where, self.connection, ordering=self.ordering)
            except NotSupportedError as e:
                # Mark this query as unsupported and return
                self.unsupported_query_message = str(e)
                return

        # DISABLE PROJECTION IF WE ARE FILTERING ON ONE OF THE PROJECTION_FIELDS
        for field in self.projection or []:
            if field in columns:
                self.projection = None
                break
        try:
            # If the PK was queried, we switch it in our queried
            # fields store with __key__
            pk_index = self.queried_fields.index(self.pk_col)
            self.queried_fields[pk_index] = "__key__"
        except ValueError:
            pass

    def execute(self):
        if self.unsupported_query_message:
            raise NotSupportedError(self.unsupported_query_message)

        self.gae_query = self._build_gae_query()
        self.results = None
        self.query_done = False
        self.aggregate_type = "count" if self.is_count else None
        self._do_fetch()

    def lower(self):
        """
            This exists solely for django-debug-toolbar compatibility.
            At some point I hope to investigate making SelectCommand a GQL string
            so that we don't need to do this hackery
        """

        return str(self).lower()

    def __eq__(self, other):
        if not isinstance(other, self.__class__):
            return False

        return self.__repr__() == other.__repr__()

    def __repr__(self):
        return "SELECT {} FROM {} WHERE {}".format(
            ", ".join(self.queried_fields or [] if not self.is_count else ["COUNT"]),
            self.db_table,
            self.where
        )

    def _set_db_table(self):
        """ Work out which Datastore kind we should actually be querying. This allows for poly
            models, i.e. non-abstract parent models which we support by storing all fields for
            both the parent model and its child models on the parent table.
        """
        inheritance_root = get_top_concrete_parent(self.model)
        self.db_table = inheritance_root._meta.db_table

    def _validate_query_is_possible(self, query):
        """ Given the *django* query, check the following:
            - The query only has one inequality filter
            - The query does no joins
            - The query ordering is compatible with the filters
        """
        # Check for joins, we ignore select related tables as they aren't actually used (the connector marks select
        # related as unsupported in its features)
        tables = [ k for k, v in query.alias_refcount.items() if v ]
        inherited_tables = set([x._meta.db_table for x in query.model._meta.parents ])
        select_related_tables = set([y[0][0] for y in query.related_select_cols ])
        tables = set(tables) - inherited_tables - select_related_tables

        if len(tables) > 1:
            raise NotSupportedError("""
                The appengine database connector does not support JOINs. The requested join map follows\n
                %s
            """ % query.join_map)

        if query.aggregates:
            if query.aggregates.keys() == [ None ]:
                agg_col = query.aggregates[None].col
                opts = self.model._meta
                if agg_col != "*" and agg_col != (opts.db_table, opts.pk.column):
                    raise NotSupportedError("Counting anything other than '*' or the primary key is not supported")
            else:
                raise NotSupportedError("Unsupported aggregate query")

    def _build_gae_query(self):
        """ Build and return the Datastore Query object. """
        query_kwargs = {
            "kind": str(self.db_table)
        }

        if self.distinct:
            if self.projection:
                query_kwargs["distinct"] = True
            else:
                logging.warning("Ignoring distinct on a query where a projection wasn't possible")

        if self.keys_only:
            query_kwargs["keys_only"] = self.keys_only
        elif self.projection:
            query_kwargs["projection"] = self.projection

        query = Query(
            **query_kwargs
        )

        if has_concrete_parents(self.model) and not self.model._meta.proxy:
            query["class ="] = self.model._meta.db_table

        ordering = []
        for order in self.ordering:
            if isinstance(order, (long, int)):
                direction = datastore.Query.ASCENDING if order == 1 else datastore.Query.DESCENDING
                order = self.queried_fields[0]
            else:
                direction = datastore.Query.DESCENDING if order.startswith("-") else datastore.Query.ASCENDING
                order = order.lstrip("-")

            if order == self.model._meta.pk.column or order == "pk":
                order = "__key__"

            #Flip the ordering if someone called reverse() on the queryset
            if not self.original_query.standard_ordering:
                direction = datastore.Query.DESCENDING if direction == datastore.Query.ASCENDING else datastore.Query.ASCENDING

            ordering.append((order, direction))

        def process_and_branch(query, and_branch):
            for child in and_branch[-1]:
                column, op, value = child[1]

            # for column, op, value in and_branch[-1]:
                if column == self.pk_col:
                    column = "__key__"

                    #FIXME: This EmptyResultSet check should happen during normalization so that Django doesn't count it as a query
                    if op == "=" and "__key__ =" in query and query["__key__ ="] != value:
                        # We've already done an exact lookup on a key, this query can't return anything!
                        raise EmptyResultSet()

                    if not isinstance(value, datastore.Key):
                        try:
                            value = get_datastore_key(self.model, value)
                        except (datastore_errors.BadValueError, datastore_errors.BadArgumentError):
                            # A key couldn't be constructed from this value, so no such entity can exist
                            raise EmptyResultSet()

                key = "%s %s" % (column, op)
                try:
                    if isinstance(value, basestring):
                        value = coerce_unicode(value)

                    if key in query:
                        if type(query[key]) == list:
                            if value not in query[key]:
                                query[key].append(value)
                        else:
                            if query[key] != value:
                                query[key] = [ query[key], value ]
                    else:
                        query[key] = value
                except datastore_errors.BadFilterError as e:
                    raise NotSupportedError(str(e))

        if self.where:
            queries = []

            # print query._Query__kind, self.where

            for and_branch in self.where[1]:
                # Duplicate the query for all the "OR"s
                queries.append(Query(**query_kwargs))
                queries[-1].update(query)  # Make sure we copy across filters (e.g. class =)
                try:
                    if and_branch[0] == "LIT":
                        and_branch = ("AND", [and_branch])
                    process_and_branch(queries[-1], and_branch)
                except EmptyResultSet:
                    # This is a little hacky but basically if there is only one branch in the or, and it raises
                    # and EmptyResultSet, then we just bail, however if there is more than one branch the query the
                    # query might still return something. This logic needs cleaning up and moving to the DNF phase
                    if len(self.where[1]) == 1:
                        return NoOpQuery()
                    else:
                        queries.pop()

            if not queries:
                return NoOpQuery()

            included_pks = [ qry["__key__ ="] for qry in queries if "__key__ =" in qry ]
            if len(included_pks) == len(queries): # If all queries have a key, we can perform a Get
                return QueryByKeys(self.model, queries, ordering) # Just use whatever query to determine the matches
            else:
                if len(queries) > 1:
                    # Disable keys only queries for MultiQuery
                    new_queries = []
                    for i, query in enumerate(queries):
                        if i > 30:
                            raise NotSupportedError("Too many subqueries (max: 30, got {}). Probably cause too many IN/!= filters".format(
                                len(queries)
                            ))
                        qry = Query(query._Query__kind, projection=query._Query__query_options.projection)
                        qry.update(query)
                        try:
                            qry.Order(*ordering)
                        except datastore_errors.BadArgumentError as e:
                            raise NotSupportedError(e)

                        new_queries.append(qry)

                    query = datastore.MultiQuery(new_queries, ordering)
                else:
                    query = queries[0]
                    try:
                        query.Order(*ordering)
                    except datastore_errors.BadArgumentError as e:
                        raise NotSupportedError(e)
        else:
            try:
                query.Order(*ordering)
            except datastore_errors.BadArgumentError as e:
                raise NotSupportedError(e)

        # If the resulting query was unique, then wrap as a unique query which
        # will hit the cache first
        unique_identifier = query_is_unique(self.model, query)
        if unique_identifier:
            return UniqueQuery(unique_identifier, query, self.model)

        DJANGAE_LOG.debug("Select query: {0}, {1}".format(self.model.__name__, self.where))

        return query

    def _do_fetch(self):
        assert not self.results

        # If we're manually excluding PKs, and we've specified a limit to the results
        # we need to make sure that we grab more than we were asked for otherwise we could filter
        # out too many! These are again limited back to the original request limit
        # while we're processing the results later
        excluded_pk_count = 0
        if self.excluded_pks and self.limits[1]:
            excluded_pk_count = len(self.excluded_pks)
            self.limits = tuple([self.limits[0], self.limits[1] + excluded_pk_count])

        self.results = self._run_query(
            aggregate_type=self.aggregate_type,
            start=self.limits[0],
            limit=None if self.limits[1] is None else (self.limits[1] - (self.limits[0] or 0))
        )

        # Ensure that the results returned is reset
        self.results_returned = 0

        if excluded_pk_count:
            # Reset the upper limit if we adjusted it above
            self.limits = tuple([self.limits[0], self.limits[1] - excluded_pk_count])

        self.query_done = True

    def _run_query(self, limit=None, start=None, aggregate_type=None):
        if aggregate_type is None:
            results = self.gae_query.Run(limit=limit, offset=start)
            if self.keys_only:
                # If we did a keys_only query for performance, we need to wrap the result
                results = convert_keys_to_entities(results)

        elif self.aggregate_type == "count":
            return self.gae_query.Count(limit=limit, offset=start)
        else:
            raise RuntimeError("Unsupported query type")

        def lazy_results():
            for result in results:
                if self.extra_select:
                    yield _apply_extra_to_entity(self.extra_select, result, self.pk_col)
                else:
                    yield result
        return lazy_results()


    def next_result(self):
        if self.limits[1]:
            if self.results_returned >= self.limits[1] - (self.limits[0] or 0):
                raise StopIteration()

        while True:
            x = self.results.next()

            if isinstance(x, datastore.Key):
                if x in self.excluded_pks:
                    continue
            elif x.key() in self.excluded_pks:
                continue

            if self.distinct_on_field: #values for distinct queries
                value = x[self.distinct_on_field]
                value = self.distinct_field_convertor(value)

                if value in self.distinct_values:
                    continue
                else:
                    self.distinct_values.add(value)
                    # Insert modified value into entity before returning the entity. This is dirty,
                    # but Cursor.fetchone (which calls this) wants the entity ID and yet also wants
                    # the correct value for this field. The alternative would be to call
                    # self.distinct_field_convertor again in Cursor.fetchone, but that's wasteful.
                    x[self.distinct_on_field] = value

            self.results_returned += 1
            return x

class FlushCommand(object):
    """
        sql_flush returns the SQL statements to flush the database,
        which are then executed by cursor.execute()

        We instead return a list of FlushCommands which are called by
        our cursor.execute
    """
    def __init__(self, table):
        self.table = table

    def execute(self):
        table = self.table
        query = datastore.Query(table, keys_only=True)
        while query.Count():
            datastore.Delete(query.Run())

        # Delete the markers we need to
        from djangae.db.constraints import UniqueMarker
        query = datastore.Query(UniqueMarker.kind(), keys_only=True)
        query["__key__ >="] = datastore.Key.from_path(UniqueMarker.kind(), self.table)
        query["__key__ <"] = datastore.Key.from_path(UniqueMarker.kind(), u"{}{}".format(self.table, u'\ufffd'))
        while query.Count():
            datastore.Delete(query.Run())

        cache.clear()
        clear_context_cache()

@db.non_transactional
def reserve_id(kind, id_or_name):
    from google.appengine.api.datastore import _GetConnection
    key = datastore.Key.from_path(kind, id_or_name)
    _GetConnection()._async_reserve_keys(None, [key])


class InsertCommand(object):
    def __init__(self, connection, model, objs, fields, raw):
        self.has_pk = any([x.primary_key for x in fields])
        self.entities = []
        self.included_keys = []
        self.model = model

        for obj in objs:
            if self.has_pk:
                # We must convert the PK value here, even though this normally happens in django_instance_to_entity otherwise
                # custom PK fields don't work properly
                value = model._meta.pk.get_db_prep_save(model._meta.pk.pre_save(obj, True), connection)
                self.included_keys.append(get_datastore_key(model, value) if value else None)
                if not self.model._meta.pk.blank and self.included_keys[-1] is None:
                    raise IntegrityError("You must specify a primary key value for {} instances".format(model))
            else:
                # We zip() self.entities and self.included_keys in execute(), so they should be the same length
                self.included_keys.append(None)

            self.entities.append(
                django_instance_to_entity(connection, model, fields, raw, obj)
            )

    def execute(self):
        if self.has_pk and not has_concrete_parents(self.model):
            results = []
            # We are inserting, but we specified an ID, we need to check for existence before we Put()
            # We do it in a loop so each check/put is transactional - because it's an ancestor query it shouldn't
            # cost any entity groups

            was_in_transaction = datastore.IsInTransaction()

            for key, ent in zip(self.included_keys, self.entities):
                @db.transactional
                def txn():
                    if key is not None:
                        if utils.key_exists(key):
                            raise IntegrityError("Tried to INSERT with existing key")

                    id_or_name = key.id_or_name()
                    if isinstance(id_or_name, basestring) and id_or_name.startswith("__"):
                        raise NotSupportedError("Datastore ids cannot start with __. Id was %s" % id_or_name)

                    if not constraints.constraint_checks_enabled(self.model):
                        # Fast path, just insert
                        results.append(datastore.Put(ent))
                    else:
                        markers = constraints.acquire(self.model, ent)
                        try:
                            results.append(datastore.Put(ent))
                            if not was_in_transaction:
                                # We can cache if we weren't in a transaction before this little nested one
                                caching.add_entity_to_cache(self.model, ent, caching.CachingSituation.DATASTORE_GET_PUT)
                        except:
                            # Make sure we delete any created markers before we re-raise
                            constraints.release_markers(markers)
                            raise

                # Make sure we notify app engine that we are using this ID
                # FIXME: Copy ancestor across to the template key
                reserve_id(key.kind(), key.id_or_name())

                txn()

            return results
        else:

            if not constraints.constraint_checks_enabled(self.model):
                # Fast path, just bulk insert
                results = datastore.Put(self.entities)
                for entity in self.entities:
                    caching.add_entity_to_cache(self.model, entity, caching.CachingSituation.DATASTORE_PUT)
                return results
            else:
                markers = []
                try:
                    #FIXME: We should rearrange this so that each entity is handled individually like above. We'll
                    # lose insert performance, but gain consistency on errors which is more important
                    markers = constraints.acquire_bulk(self.model, self.entities)

                    results = datastore.Put(self.entities)
                    for entity in self.entities:
                        caching.add_entity_to_cache(self.model, entity, caching.CachingSituation.DATASTORE_PUT)

                except:
                    to_delete = chain(*markers)
                    constraints.release_markers(to_delete)
                    raise

                for ent, k, m in zip(self.entities, results, markers):
                    ent.__key = k
                    constraints.update_instance_on_markers(ent, m)

                return results


class DeleteCommand(object):
    def __init__(self, connection, query):
        self.select = SelectCommand(connection, query, keys_only=True)

    def execute(self):
        self.select.execute()

        # This is a little bit more inefficient than just doing a keys_only query and
        # sending it to delete, but I think this is the sacrifice to make for the unique caching layer
        keys = []

        def spawn_query(kind, key):
            qry = Query(kind)
            qry["__key__ ="] = key
            return qry

        queries = [spawn_query(self.select.db_table, x.key()) for x in self.select.results]
        if not queries:
            return

        for entity in QueryByKeys(self.select.model, queries, []).Run():
            keys.append(entity.key())

            # Delete constraints if that's enabled
            if constraints.constraint_checks_enabled(self.select.model):
                constraints.release(self.select.model, entity)

            caching.remove_entity_from_cache_by_key(entity.key())
        datastore.Delete(keys)


class UpdateCommand(object):
    def __init__(self, connection, query):
        self.model = query.model
        self.select = SelectCommand(connection, query, keys_only=True)
        self.values = query.values
        self.connection = connection

    @db.transactional
    def _update_entity(self, key):
        caching.remove_entity_from_cache_by_key(key)

        try:
            result = datastore.Get(key)
        except datastore_errors.EntityNotFoundError:
            # Return false to indicate update failure
            return False

        original = copy.deepcopy(result)

        instance_kwargs = {field.attname:value for field, param, value in self.values}

        # Note: If you replace MockInstance with self.model, you'll find that some delete
        # tests fail in the test app. This is because any unspecified fields would then call
        # get_default (even though we aren't going to use them) which may run a query which
        # fails inside this transaction. Given as we are just using MockInstance so that we can
        # call django_instance_to_entity it on it with the subset of fields we pass in,
        # what we have is fine.
        instance = MockInstance(**instance_kwargs)

        # Update the entity we read above with the new values
        result.update(django_instance_to_entity(
            self.connection, self.model,
            [ x[0] for x in self.values],  # Pass in the fields that were updated
            True, instance)
        )

        if not constraints.constraint_checks_enabled(self.model):
            # The fast path, no constraint checking
            datastore.Put(result)
            caching.add_entity_to_cache(self.model, result, caching.CachingSituation.DATASTORE_PUT)
        else:
            to_acquire, to_release = constraints.get_markers_for_update(self.model, original, result)

            # Acquire first, because if that fails then we don't want to alter what's already there
            constraints.acquire_identifiers(to_acquire, result.key())
            try:
                datastore.Put(result)
                caching.add_entity_to_cache(self.model, result, caching.CachingSituation.DATASTORE_PUT)
            except:
                constraints.release_identifiers(to_acquire)
                raise
            else:
                # Now we release the ones we don't want anymore
                constraints.release_identifiers(to_release)

        # Return true to indicate update success
        return True

    def execute(self):
        self.select.execute()

        results = self.select.results

        i = 0
        for result in results:
            if self._update_entity(result.key()):
                # Only increment the count if we successfully updated
                i += 1

        return i
