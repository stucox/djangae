import os

from cStringIO import StringIO
import datetime
import unittest
from string import letters
from hashlib import md5
import decimal

# LIBRARIES
from django.core.files.uploadhandler import StopFutureHandlers
from django.core.cache import cache
from django.core.exceptions import ValidationError
from django.db import connections
from django.db import DataError, models
from django.db.models.query import Q
from django.forms import ModelForm
from django.test import RequestFactory
from django.utils.safestring import SafeText
from django.forms.models import modelformset_factory
from django.db.models.sql.datastructures import EmptyResultSet
from google.appengine.api.datastore_errors import EntityNotFoundError, BadValueError
from google.appengine.api import datastore
from google.appengine.ext import deferred
from google.appengine.api import taskqueue
from django.test.utils import override_settings
from django.contrib.contenttypes.models import ContentType
from django.core.exceptions import FieldError

# DJANGAE
from djangae.contrib import sleuth
from djangae.test import inconsistent_db, TestCase

from django.db import IntegrityError, NotSupportedError
from djangae.db.constraints import UniqueMarker, UniquenessMixin
from djangae.db.unique_utils import _unique_combinations, unique_identifiers_from_entity
from djangae.indexing import add_special_index
from djangae.db.utils import entity_matches_query, decimal_to_string, normalise_field_value
from djangae.db.caching import disable_cache
from djangae.db import transaction
from djangae.fields import ComputedCharField, ShardedCounterField, SetField, ListField, GenericRelationField, RelatedSetField
from djangae.models import CounterShard
from djangae.db.backends.appengine.dnf import parse_dnf
from djangae.storage import BlobstoreFileUploadHandler
from djangae.wsgi import DjangaeApplication
from djangae.core import paginator
from django.template import Template, Context

try:
    import webtest
except ImportError:
    webtest = NotImplemented


class TestUser(models.Model):
    username = models.CharField(max_length=32)
    email = models.EmailField()
    last_login = models.DateField(auto_now_add=True)
    field2 = models.CharField(max_length=32)

    def __unicode__(self):
        return self.username

    class Meta:
        app_label = "djangae"

class ModelWithNullableCharField(models.Model):
    field1 = models.CharField(max_length=500, null=True)
    some_id = models.IntegerField(default=0)

    class Meta:
        app_label = "djangae"

class UniqueModel(models.Model):
    unique_field = models.CharField(max_length=100, unique=True)
    unique_combo_one = models.IntegerField(blank=True, default=0)
    unique_combo_two = models.CharField(max_length=100, blank=True, default="")

    unique_relation = models.ForeignKey('self', null=True, blank=True, unique=True)

    unique_set_field = SetField(models.CharField(max_length=500), unique=True)
    unique_list_field = ListField(models.CharField(max_length=500), unique=True)

    unique_together_list_field = ListField(models.IntegerField())

    class Meta:
        unique_together = [
            ("unique_combo_one", "unique_combo_two"),
            ("unique_together_list_field", "unique_combo_one")
        ]

        app_label = "djangae"


class UniqueModelWithLongPK(models.Model):
    long_pk = models.CharField(max_length=500, primary_key=True)
    unique_field = models.IntegerField(unique=True)


class IntegerModel(models.Model):
    integer_field = models.IntegerField()

    class Meta:
        app_label = "djangae"


class TestFruit(models.Model):
    name = models.CharField(primary_key=True, max_length=32)
    origin = models.CharField(max_length=32, default="Unknown")
    color = models.CharField(max_length=100)
    is_mouldy = models.BooleanField(default=False)

    class Meta:
        ordering = ("color",)
        app_label = "djangae"

    def __unicode__(self):
        return self.name

    def __repr__(self):
        return "<TestFruit: name={}, color={}>".format(self.name, self.color)

class Permission(models.Model):
    user = models.ForeignKey(TestUser)
    perm = models.CharField(max_length=32)

    def __unicode__(self):
        return u"{0} for {1}".format(self.perm, self.user)

    class Meta:
        ordering = ('user__username', 'perm')
        app_label = "djangae"


class SelfRelatedModel(models.Model):
    related = models.ForeignKey('self', blank=True, null=True)

    class Meta:
        app_label = "djangae"

class MultiTableParent(models.Model):
    parent_field = models.CharField(max_length=32)

    class Meta:
        app_label = "djangae"

class MultiTableChildOne(MultiTableParent):
    child_one_field = models.CharField(max_length=32)

    class Meta:
        app_label = "djangae"


class MultiTableChildTwo(MultiTableParent):
    child_two_field = models.CharField(max_length=32)

    class Meta:
        app_label = "djangae"


class Relation(models.Model):
    class Meta:
        app_label = "djangae"


class Related(models.Model):
    headline = models.CharField(max_length=500)
    relation = models.ForeignKey(Relation)

    class Meta:
        app_label = "djangae"


class NullDate(models.Model):
    date = models.DateField(null=True, default=None)
    datetime = models.DateTimeField(null=True, default=None)
    time = models.TimeField(null=True, default=None)

    class Meta:
        app_label = "djangae"


class NullDateSet(models.Model):
    dates = RelatedSetField(NullDate, blank=True, unique=True)

    class Meta:
        app_label = "djangae"


class ModelWithUniques(models.Model):
    name = models.CharField(max_length=64, unique=True)

    class Meta:
        app_label = "djangae"


class ModelWithUniquesOnForeignKey(models.Model):
    name = models.CharField(max_length=64, unique=True)
    related_name = models.ForeignKey(ModelWithUniques, unique=True)

    class Meta:
        unique_together = [("name", "related_name")]
        app_label = "djangae"


class ModelWithDates(models.Model):
    start = models.DateField()
    end = models.DateField()

    class Meta:
        app_label = "djangae"


class ModelWithUniquesAndOverride(models.Model):
    name = models.CharField(max_length=64, unique=True)

    class Djangae:
        disable_constraint_checks = False

    class Meta:
        app_label = "djangae"


class ISOther(models.Model):
    name = models.CharField(max_length=500)

    def __unicode__(self):
        return "%s:%s" % (self.pk, self.name)

    class Meta:
        app_label = "djangae"

class RelationWithoutReverse(models.Model):
    name = models.CharField(max_length=500)

    class Meta:
        app_label = "djangae"


class ISModel(models.Model):
    related_things = RelatedSetField(ISOther)
    limted_related = RelatedSetField(RelationWithoutReverse, limit_choices_to={'name': 'banana'}, related_name="+")
    children = RelatedSetField("self", related_name="+")

    class Meta:
        app_label = "djangae"


class RelationWithOverriddenDbTable(models.Model):
    class Meta:
        db_table = "bananarama"
        app_label = "djangae"


class GenericRelationModel(models.Model):
    relation_to_content_type = GenericRelationField(ContentType, null=True)
    relation_to_weird = GenericRelationField(RelationWithOverriddenDbTable, null=True)

    class Meta:
        app_label = "djangae"


class SpecialIndexesModel(models.Model):
    name = models.CharField(max_length=255)

    def __unicode__(self):
        return self.name

    class Meta:
        app_label = "djangae"


class DateTimeModel(models.Model):
    datetime_field = models.DateTimeField(auto_now_add=True)
    date_field = models.DateField(auto_now_add=True)

    class Meta:
        app_label = "djangae"

class PaginatorModel(models.Model):
    foo = models.IntegerField()

    class Meta:
        app_label = "djangae"


class IterableFieldModel(models.Model):
    set_field = SetField(models.CharField(max_length=1))
    list_field = ListField(models.CharField(max_length=1))

    class Meta:
        app_label = "djangae"


class BackendTests(TestCase):
    def test_entity_matches_query(self):
        entity = datastore.Entity("test_model")
        entity["name"] = "Charlie"
        entity["age"] = 22

        query = datastore.Query("test_model")
        query["name ="] = "Charlie"
        self.assertTrue(entity_matches_query(entity, query))

        query["age >="] = 5
        self.assertTrue(entity_matches_query(entity, query))
        del query["age >="]

        query["age <"] = 22
        self.assertFalse(entity_matches_query(entity, query))
        del query["age <"]

        query["age <="] = 22
        self.assertTrue(entity_matches_query(entity, query))
        del query["age <="]

        query["name ="] = "Fred"
        self.assertFalse(entity_matches_query(entity, query))

        # If the entity has a list field, then if any of them match the
        # query then it's a match
        entity["name"] = [ "Bob", "Fred", "Dave" ]
        self.assertTrue(entity_matches_query(entity, query))  # ListField test

    def test_defaults(self):
        fruit = TestFruit.objects.create(name="Apple", color="Red")
        self.assertEqual("Unknown", fruit.origin)

        instance = datastore.Get(datastore.Key.from_path(TestFruit._meta.db_table, fruit.pk))
        del instance["origin"]
        datastore.Put(instance)

        fruit = TestFruit.objects.get()
        self.assertIsNone(fruit.origin)
        fruit.save()

        fruit = TestFruit.objects.get()
        self.assertEqual("Unknown", fruit.origin)


    def test_get_or_create(self):
        """
            Django's get_or_create can do the following:

            1. get(**lookup) -> throws DoesNotExist
            2. Catches DoesNotExist
            3. create() -> throws IntegrityError
            4. get(**lookup)

            This test proves that we throw the right kind of error at step 3 when
            unique constraints are violated.
        """

        def wrap_get(func):
            def _wrapped(*args, **kwargs):
                try:
                    if _wrapped.calls == 0:
                        raise UniqueModel.DoesNotExist()
                    else:
                        return func(*args, **kwargs)
                finally:
                    _wrapped.calls += 1

            _wrapped.calls = 0
            return _wrapped

        from django.db.models import query
        wrapped_get = wrap_get(query.QuerySet.get)

        UniqueModel.objects.create(unique_field="Test")

        with disable_cache():
            with sleuth.switch("django.db.models.query.QuerySet.get", wrapped_get):
                instance, created = UniqueModel.objects.get_or_create(unique_field="Test")
                self.assertFalse(created)

    def test_setting_non_null_null_throws_integrity_error(self):
        with self.assertRaises(IntegrityError):
            IntegerModel.objects.create(integer_field=None)

        with self.assertRaises(IntegrityError):
            instance = IntegerModel()
            instance.integer_field = None
            instance.save()

        with self.assertRaises(IntegrityError):
            instance = IntegerModel.objects.create(integer_field=1)
            instance = IntegerModel.objects.get()
            instance.integer_field = None
            instance.save()

    def test_normalise_field_value(self):
        self.assertEqual(u'0000475231073257', normalise_field_value(decimal.Decimal(475231073257)))
        self.assertEqual(u'-0000475231073257', normalise_field_value(decimal.Decimal(-475231073257)))
        self.assertEqual(u'0000000004752311', normalise_field_value(decimal.Decimal(4752310.73257)))
        self.assertEqual(u'0000004752310733', normalise_field_value(decimal.Decimal(4752310732.57)))
        self.assertEqual(datetime.datetime(2015, 1, 27, 2, 46, 8, 584258), normalise_field_value(datetime.datetime(2015, 1, 27, 2, 46, 8, 584258)))

    def test_decimal_to_string(self):
        self.assertEqual(u'0002312487812767', decimal_to_string(decimal.Decimal(2312487812767)))
        self.assertEqual(u'-0002312487812767', decimal_to_string(decimal.Decimal(-2312487812767)))
        self.assertEqual(u'002312487812', decimal_to_string(decimal.Decimal(2312487812), 12))
        self.assertEqual(u'002387812.320', decimal_to_string(decimal.Decimal(2387812.32), 12, 3))
        self.assertEqual(u'-002387812.513', decimal_to_string(decimal.Decimal(-2387812.513212), 12, 3))
        self.assertEqual(u'0237812.000', decimal_to_string(decimal.Decimal(237812), 10, 3))
        self.assertEqual(u'-0237812.210', decimal_to_string(decimal.Decimal(-237812.21), 10, 3))

    def test_gae_conversion(self):
        # A PK IN query should result in a single get by key

        with sleuth.switch("djangae.db.backends.appengine.commands.datastore.Get", lambda *args, **kwargs: []) as get_mock:
            list(TestUser.objects.filter(pk__in=[1, 2, 3]))  # Force the query to run
            self.assertEqual(1, get_mock.call_count)

        with sleuth.switch("djangae.db.backends.appengine.commands.datastore.Query.Run", lambda *args, **kwargs: []) as query_mock:
            list(TestUser.objects.filter(username="test"))
            self.assertEqual(1, query_mock.call_count)

        with sleuth.switch("djangae.db.backends.appengine.commands.datastore.MultiQuery.Run", lambda *args, **kwargs: []) as query_mock:
            list(TestUser.objects.filter(username__in=["test", "cheese"]))
            self.assertEqual(1, query_mock.call_count)

        with sleuth.switch("djangae.db.backends.appengine.commands.datastore.Get", lambda *args, **kwargs: []) as get_mock:
            list(TestUser.objects.filter(pk=1))
            self.assertEqual(1, get_mock.call_count)

        #FIXME: Issue #80
        with self.assertRaises(NotSupportedError):
            with sleuth.switch("djangae.db.backends.appengine.commands.datastore.MultiQuery.Run", lambda *args, **kwargs: []) as query_mock:
                list(TestUser.objects.exclude(username__startswith="test"))
                self.assertEqual(1, query_mock.call_count)

        with sleuth.switch("djangae.db.backends.appengine.commands.datastore.Get", lambda *args, **kwargs: []) as get_mock:
            list(TestUser.objects.filter(pk__in=[1, 2, 3, 4, 5, 6, 7, 8]).
                filter(username__in=["test", "test2", "test3"]).filter(email__in=["test@example.com", "test2@example.com"]))

            self.assertEqual(1, get_mock.call_count)

    def test_range_behaviour(self):
        IntegerModel.objects.create(integer_field=5)
        IntegerModel.objects.create(integer_field=10)
        IntegerModel.objects.create(integer_field=15)

        self.assertItemsEqual([10], IntegerModel.objects.filter(integer_field__range=(6, 14)).values_list("integer_field", flat=True))
        self.assertItemsEqual([5, 10, 15], IntegerModel.objects.filter(integer_field__range=(5, 15)).order_by("integer_field").values_list("integer_field", flat=True))
        self.assertItemsEqual([5, 15], IntegerModel.objects.exclude(integer_field__range=(6, 14)).values_list("integer_field", flat=True))

    def test_exclude_nullable_field(self):
        instance = ModelWithNullableCharField.objects.create(some_id=999) # Create a nullable thing
        instance2 = ModelWithNullableCharField.objects.create(some_id=999, field1="test") # Create a nullable thing
        self.assertItemsEqual([instance], ModelWithNullableCharField.objects.filter(some_id=999).exclude(field1="test").all())

        instance.field1 = "bananas"
        instance.save()

        self.assertEqual(instance, ModelWithNullableCharField.objects.filter(some_id=999).exclude(field1="test")[0])


    def test_null_date_field(self):
        null_date = NullDate()
        null_date.save()

        null_date = NullDate.objects.get()
        self.assertIsNone(null_date.date)
        self.assertIsNone(null_date.time)
        self.assertIsNone(null_date.datetime)

    def test_convert_unicode_subclasses_to_unicode(self):
        # The App Engine SDK raises BadValueError if you try saving a SafeText
        # string to a CharField. Djangae explicitly converts it to unicode.
        grue = SafeText(u'grue')

        self.assertIsInstance(grue, unicode)
        self.assertNotEqual(type(grue), unicode)

        obj = TestFruit.objects.create(name=u'foo', color=grue)
        obj = TestFruit.objects.get(pk=obj.pk)
        self.assertEqual(type(obj.color), unicode)

        obj = TestFruit.objects.filter(color=grue)[0]
        self.assertEqual(type(obj.color), unicode)

    def test_notsupportederror_thrown_on_too_many_inequalities(self):
        TestFruit.objects.create(name="Apple", color="Green", origin="England")
        pear = TestFruit.objects.create(name="Pear", color="Green")
        banana = TestFruit.objects.create(name="Banana", color="Yellow")

        # Excluding one field is fine
        self.assertItemsEqual([pear, banana], list(TestFruit.objects.exclude(name="Apple")))

        # Excluding a field, and doing a > or < on another is not so fine
        with self.assertRaises(NotSupportedError):
            self.assertEqual(pear, TestFruit.objects.exclude(origin="England").filter(color__lt="Yellow").get())

        # Same with excluding two fields
        with self.assertRaises(NotSupportedError):
            list(TestFruit.objects.exclude(origin="England").exclude(color="Yellow"))

        # But apparently excluding the same field twice is OK
        self.assertItemsEqual([banana], list(TestFruit.objects.exclude(origin="England").exclude(name="Pear").order_by("origin")))

    def test_excluding_pks_is_emulated(self):
        apple = TestFruit.objects.create(name="Apple", color="Green", is_mouldy=True, origin="England")
        banana = TestFruit.objects.create(name="Banana", color="Yellow", is_mouldy=True, origin="Dominican Republic")
        cherry = TestFruit.objects.create(name="Cherry", color="Red", is_mouldy=True, origin="Germany")
        pear = TestFruit.objects.create(name="Pear", color="Green", origin="England")

        self.assertEqual([apple, pear], list(TestFruit.objects.filter(origin__lt="Germany").exclude(pk=banana.pk).exclude(pk=cherry.pk).order_by("origin")))
        self.assertEqual([apple, cherry], list(TestFruit.objects.exclude(origin="Dominican Republic").exclude(pk=pear.pk).order_by("origin")))
        self.assertEqual([], list(TestFruit.objects.filter(is_mouldy=True).filter(color="Green", origin__gt="England").exclude(pk=pear.pk).order_by("-origin")))
        self.assertEqual([cherry, banana], list(TestFruit.objects.exclude(pk=pear.pk).order_by("-name")[:2]))
        self.assertEqual([banana, apple], list(TestFruit.objects.exclude(pk=pear.pk).order_by("origin", "name")[:2]))

    def test_datetime_fields(self):
        date = datetime.datetime.today()
        dt = datetime.datetime.now()
        time = datetime.time(0,0,0)

        # check if creating objects work
        obj = NullDate.objects.create(date=date, datetime=dt, time=time)

        # check if filtering objects work
        self.assertItemsEqual([obj], NullDate.objects.filter(datetime=dt))
        self.assertItemsEqual([obj], NullDate.objects.filter(date=date))
        self.assertItemsEqual([obj], NullDate.objects.filter(time=time))

        # check if updating objects work
        obj.date = date + datetime.timedelta(days=1)
        obj.datetime = dt + datetime.timedelta(days=1)
        obj.time = datetime.time(23,0,0)
        obj.save()
        self.assertItemsEqual([obj], NullDate.objects.filter(datetime=obj.datetime))
        self.assertItemsEqual([obj], NullDate.objects.filter(date=obj.date))
        self.assertItemsEqual([obj], NullDate.objects.filter(time=obj.time))

    def test_related_datetime_nullable(self):
        date = datetime.datetime.today()
        dt = datetime.datetime.now()
        time = datetime.time(0,0,0)

        date_set = NullDateSet.objects.create()
        empty_obj = NullDate.objects.create(date=None, datetime=None, time=None)
        date_set.dates.add(empty_obj)

        obj = NullDate.objects.create(date=date, datetime=dt, time=time)
        date_set.dates.add(obj)
        date_set.save()

        # check if filtering/excluding of None works in RelatedSetField
        self.assertItemsEqual([obj], date_set.dates.filter(datetime__isnull=False))
        self.assertItemsEqual([obj], date_set.dates.filter(date__isnull=False))
        self.assertItemsEqual([obj], date_set.dates.filter(time__isnull=False))

        self.assertItemsEqual([obj], date_set.dates.exclude(datetime=None))
        self.assertItemsEqual([obj], date_set.dates.exclude(date=None))
        self.assertItemsEqual([obj], date_set.dates.exclude(time=None))

        # sorting should work too
        self.assertItemsEqual([obj, empty_obj], date_set.dates.order_by('datetime'))
        self.assertItemsEqual([empty_obj, obj], date_set.dates.order_by('-datetime'))
        self.assertItemsEqual([obj, empty_obj], date_set.dates.order_by('date'))
        self.assertItemsEqual([empty_obj, obj], date_set.dates.order_by('-date'))
        self.assertItemsEqual([obj, empty_obj], date_set.dates.order_by('time'))
        self.assertItemsEqual([empty_obj, obj], date_set.dates.order_by('-time'))


class ModelFormsetTest(TestCase):
    def test_reproduce_index_error(self):
        class TestModelForm(ModelForm):
            class Meta:
                model = TestUser
                fields = ("username", "email", "field2")

        test_model = TestUser.objects.create(username='foo', field2='bar')
        TestModelFormSet = modelformset_factory(TestUser, form=TestModelForm, extra=0)
        TestModelFormSet(queryset=TestUser.objects.filter(pk=test_model.pk))

        data = {
            'form-INITIAL_FORMS': 0,
            'form-MAX_NUM_FORMS': 0,
            'form-TOTAL_FORMS': 0,
            'form-0-id': test_model.id,
            'form-0-field1': 'foo_1',
            'form-0-field2': 'bar_1',
        }
        factory = RequestFactory()
        request = factory.post('/', data=data)

        TestModelFormSet(request.POST, request.FILES)


class CacheTests(TestCase):

    def test_cache_set(self):
        cache.set('test?', 'yes!')
        self.assertEqual(cache.get('test?'), 'yes!')

    def test_cache_timeout(self):
        cache.set('test?', 'yes!', 1)
        import time
        time.sleep(1)
        self.assertEqual(cache.get('test?'), None)


class TransactionTests(TestCase):
    def test_atomic_decorator(self):

        @transaction.atomic
        def txn():
            TestUser.objects.create(username="foo", field2="bar")
            raise ValueError()

        with self.assertRaises(ValueError):
            txn()

        self.assertEqual(0, TestUser.objects.count())

        # Test on a class method: should pass correct number of args
        class Cls(object):
            @transaction.atomic
            def txn(self, arg):
                return arg

        obj = Cls()
        self.assertEqual(7, obj.txn(7))

    def test_nested_decorator(self):
        # Nested decorator pattern we discovered can cause a connection_stack
        # underflow.

        @transaction.atomic
        def inner_txn():
            pass

        @transaction.atomic
        def outer_txn():
            inner_txn()

        # Calling inner_txn first puts it in a state which means it doesn't
        # then behave properly in a nested transaction.
        inner_txn()
        outer_txn()

    def test_interaction_with_datastore_txn(self):
        from google.appengine.ext import db
        from google.appengine.datastore.datastore_rpc import TransactionOptions

        @db.transactional(propagation=TransactionOptions.INDEPENDENT)
        def some_indie_txn(_username):
            TestUser.objects.create(username=_username)

        @db.transactional()
        def some_non_indie_txn(_username):
            TestUser.objects.create(username=_username)

        @db.transactional()
        def double_nested_transactional():
            @db.transactional(propagation=TransactionOptions.INDEPENDENT)
            def do_stuff():
                TestUser.objects.create(username="Double")
                raise ValueError()

            try:
                return do_stuff
            except:
                return

        with transaction.atomic():
            double_nested_transactional()


        @db.transactional()
        def something_containing_atomic():
            with transaction.atomic():
                TestUser.objects.create(username="Inner")

        something_containing_atomic()

        with transaction.atomic():
            with transaction.atomic():
                some_non_indie_txn("Bob1")
                some_indie_txn("Bob2")
                some_indie_txn("Bob3")

        with transaction.atomic(independent=True):
            some_non_indie_txn("Fred1")
            some_indie_txn("Fred2")
            some_indie_txn("Fred3")

    def test_atomic_context_manager(self):

        with self.assertRaises(ValueError):
            with transaction.atomic():
                TestUser.objects.create(username="foo", field2="bar")
                raise ValueError()

        self.assertEqual(0, TestUser.objects.count())

    def test_xg_argument(self):

        @transaction.atomic(xg=True)
        def txn(_username):
            TestUser.objects.create(username=_username, field2="bar")
            TestFruit.objects.create(name="Apple", color="pink")
            raise ValueError()

        with self.assertRaises(ValueError):
            txn("foo")

        self.assertEqual(0, TestUser.objects.count())
        self.assertEqual(0, TestFruit.objects.count())

        # Test on a class method: should pass correct number of args
        class Cls(object):
            @transaction.atomic(xg=True)
            def txn(self, arg):
                return arg

        obj = Cls()
        self.assertEqual(7, obj.txn(7))

    def test_independent_argument(self):
        """
            We would get a XG error if the inner transaction was not independent
        """

        @transaction.atomic
        def txn1(_username, _fruit):
            @transaction.atomic(independent=True)
            def txn2(_fruit):
                TestFruit.objects.create(name=_fruit, color="pink")
                raise ValueError()

            TestUser.objects.create(username=_username)
            txn2(_fruit)


        with self.assertRaises(ValueError):
            txn1("test", "banana")


class QueryNormalizationTests(TestCase):
    """
        The parse_dnf function takes a Django where tree, and converts it
        into a tree of one of the following forms:

        [ (column, operator, value), (column, operator, value) ] <- AND only query
        [ [(column, operator, value)], [(column, operator, value) ]] <- OR query, of multiple ANDs
    """

    def test_and_queries(self):
        connection = connections['default']

        qs = TestUser.objects.filter(username="test").all()

        self.assertEqual(('OR', [('LIT', ('username', '=', 'test'))]), parse_dnf(qs.query.where, connection=connection)[0])

        qs = TestUser.objects.filter(username="test", email="test@example.com")

        expected = ('OR', [('AND', [('LIT', ('username', '=', 'test')), ('LIT', ('email', '=', 'test@example.com'))])])

        self.assertEqual(expected, parse_dnf(qs.query.where, connection=connection)[0])
        #
        qs = TestUser.objects.filter(username="test").exclude(email="test@example.com")

        expected = ('OR', [
            ('AND', [('LIT', ('username', '=', 'test')), ('LIT', ('email', '>', 'test@example.com'))]),
            ('AND', [('LIT', ('username', '=', 'test')), ('LIT', ('email', '<', 'test@example.com'))])
        ])

        self.assertEqual(expected, parse_dnf(qs.query.where, connection=connection)[0])

        qs = TestUser.objects.filter(username__lte="test").exclude(email="test@example.com")
        expected = ('OR', [
            ('AND', [("username", "<=", "test"), ("email", ">", "test@example.com")]),
            ('AND', [("username", "<=", "test"), ("email", "<", "test@example.com")]),
        ])

        #FIXME: This will raise a BadFilterError on the datastore, we should instead raise NotSupportedError in that case
        #with self.assertRaises(NotSupportedError):
        #    parse_dnf(qs.query.where, connection=connection)

        instance = Relation(pk=1)
        qs = instance.related_set.filter(headline__startswith='Fir')

        expected = ('OR', [('AND', [('LIT', ('relation_id', '=', 1)), ('LIT', ('_idx_startswith_headline', '=', u'Fir'))])])

        norm = parse_dnf(qs.query.where, connection=connection)[0]

        self.assertEqual(expected, norm)

    def test_or_queries(self):

        connection = connections['default']

        qs = TestUser.objects.filter(
            username="python").filter(
            Q(username__in=["ruby", "jruby"]) | (Q(username="php") & ~Q(username="perl"))
        )

        # After IN and != explosion, we have...
        # (AND: (username='python', OR: (username='ruby', username='jruby', AND: (username='php', AND: (username < 'perl', username > 'perl')))))

        # Working backwards,
        # AND: (username < 'perl', username > 'perl') can't be simplified
        # AND: (username='php', AND: (username < 'perl', username > 'perl')) can become (OR: (AND: username = 'php', username < 'perl'), (AND: username='php', username > 'perl'))
        # OR: (username='ruby', username='jruby', (OR: (AND: username = 'php', username < 'perl'), (AND: username='php', username > 'perl')) can't be simplified
        # (AND: (username='python', OR: (username='ruby', username='jruby', (OR: (AND: username = 'php', username < 'perl'), (AND: username='php', username > 'perl'))
        # becomes...
        # (OR: (AND: username='python', username = 'ruby'), (AND: username='python', username='jruby'), (AND: username='python', username='php', username < 'perl') \
        #      (AND: username='python', username='php', username > 'perl')

        expected = ('OR', [
            ('AND', [('LIT', ('username', '=', 'python')), ('LIT', ('username', '=', 'ruby'))]),
            ('AND', [('LIT', ('username', '=', 'python')), ('LIT', ('username', '=', 'jruby'))]),
            ('AND', [('LIT', ('username', '=', 'python')), ('LIT', ('username', '=', 'php')), ('LIT', ('username', '>', 'perl'))]),
            ('AND', [('LIT', ('username', '=', 'python')), ('LIT', ('username', '=', 'php')), ('LIT', ('username', '<', 'perl'))])
        ])

        self.assertEqual(expected, parse_dnf(qs.query.where, connection=connection)[0])
        #

        qs = TestUser.objects.filter(username="test") | TestUser.objects.filter(username="cheese")

        expected = ('OR', [
            ('LIT', ("username", "=", "test")),
            ('LIT', ("username", "=", "cheese")),
        ])

        self.assertEqual(expected, parse_dnf(qs.query.where, connection=connection)[0])

        qs = TestUser.objects.using("default").filter(username__in=set()).values_list('email')

        with self.assertRaises(EmptyResultSet):
            parse_dnf(qs.query.where, connection=connection)

        qs = TestUser.objects.filter(username__startswith='Hello') |  TestUser.objects.filter(username__startswith='Goodbye')
        expected = ('OR', [
            ('LIT', ('_idx_startswith_username', '=', u'Hello')),
            ('LIT', ('_idx_startswith_username', '=', u'Goodbye'))
        ])
        self.assertEqual(expected, parse_dnf(qs.query.where, connection=connection)[0])

        qs = TestUser.objects.filter(pk__in=[1, 2, 3])

        expected = ('OR', [
            ('LIT', ("id", "=", datastore.Key.from_path(TestUser._meta.db_table, 1))),
            ('LIT', ("id", "=", datastore.Key.from_path(TestUser._meta.db_table, 2))),
            ('LIT', ("id", "=", datastore.Key.from_path(TestUser._meta.db_table, 3))),
        ])

        self.assertEqual(expected, parse_dnf(qs.query.where, connection=connection)[0])

        qs = TestUser.objects.filter(pk__in=[1, 2, 3]).filter(username="test")

        expected = ('OR', [
            ('AND', [
                ('LIT', (u'id', '=', datastore.Key.from_path(TestUser._meta.db_table, 1))),
                ('LIT', ('username', '=', 'test'))
            ]),
            ('AND', [
                ('LIT', (u'id', '=', datastore.Key.from_path(TestUser._meta.db_table, 2))),
                ('LIT', ('username', '=', 'test'))
            ]),
            ('AND', [
                ('LIT', (u'id', '=', datastore.Key.from_path(TestUser._meta.db_table, 3))),
                ('LIT', ('username', '=', 'test'))
            ])
        ])
        self.assertEqual(expected, parse_dnf(qs.query.where, connection=connection)[0])




class ConstraintTests(TestCase):
    """
        Tests for unique constraint handling
    """

    def test_update_updates_markers(self):
        initial_count = datastore.Query(UniqueMarker.kind()).Count()

        instance = ModelWithUniques.objects.create(name="One")

        self.assertEqual(1, datastore.Query(UniqueMarker.kind()).Count() - initial_count)

        qry = datastore.Query(UniqueMarker.kind())
        qry.Order(("created", datastore.Query.DESCENDING))

        marker = [x for x in qry.Run()][0]
        # Make sure we assigned the instance
        self.assertEqual(marker["instance"], datastore.Key.from_path(instance._meta.db_table, instance.pk))

        expected_marker = "{}|name:{}".format(ModelWithUniques._meta.db_table, md5("One").hexdigest())
        self.assertEqual(expected_marker, marker.key().id_or_name())

        instance.name = "Two"
        instance.save()

        self.assertEqual(1, datastore.Query(UniqueMarker.kind()).Count() - initial_count)
        marker = [x for x in qry.Run()][0]
        # Make sure we assigned the instance
        self.assertEqual(marker["instance"], datastore.Key.from_path(instance._meta.db_table, instance.pk))

        expected_marker = "{}|name:{}".format(ModelWithUniques._meta.db_table, md5("Two").hexdigest())
        self.assertEqual(expected_marker, marker.key().id_or_name())

    def test_conflicting_insert_throws_integrity_error(self):
        ModelWithUniques.objects.create(name="One")

        with self.assertRaises(IntegrityError):
            ModelWithUniques.objects.create(name="One")

    def test_table_flush_clears_markers_for_that_table(self):
        ModelWithUniques.objects.create(name="One")
        UniqueModel.objects.create(unique_field="One")

        from djangae.db.backends.appengine.commands import FlushCommand

        FlushCommand(ModelWithUniques._meta.db_table).execute()
        ModelWithUniques.objects.create(name="One")

        with self.assertRaises(IntegrityError):
            UniqueModel.objects.create(unique_field="One")


    def test_conflicting_update_throws_integrity_error(self):
        ModelWithUniques.objects.create(name="One")

        instance = ModelWithUniques.objects.create(name="Two")
        with self.assertRaises(IntegrityError):
            instance.name = "One"
            instance.save()

    def test_unique_combinations_are_returned_correctly(self):
        combos_one = _unique_combinations(ModelWithUniquesOnForeignKey, ignore_pk=True)
        combos_two = _unique_combinations(ModelWithUniquesOnForeignKey, ignore_pk=False)

        self.assertEqual([['name', 'related_name'], ['name'], ['related_name']], combos_one)
        self.assertEqual([['name', 'related_name'], ['id'], ['name'], ['related_name']], combos_two)

        class Entity(dict):
            def __init__(self, model, id):
                self._key = datastore.Key.from_path(model, id)

            def key(self):
                return self._key

        e1 = Entity(ModelWithUniquesOnForeignKey._meta.db_table, 1)
        e1["name"] = "One"
        e1["related_name_id"] = 1

        ids_one = unique_identifiers_from_entity(ModelWithUniquesOnForeignKey, e1)

        self.assertItemsEqual([
            u'djangae_modelwithuniquesonforeignkey|id:1',
            u'djangae_modelwithuniquesonforeignkey|name:06c2cea18679d64399783748fa367bdd',
            u'djangae_modelwithuniquesonforeignkey|related_name_id:1',
            u'djangae_modelwithuniquesonforeignkey|name:06c2cea18679d64399783748fa367bdd|related_name_id:1'
        ], ids_one)

    def test_error_on_update_doesnt_change_markers(self):
        initial_count = datastore.Query(UniqueMarker.kind()).Count()

        instance = ModelWithUniques.objects.create(name="One")

        self.assertEqual(1, datastore.Query(UniqueMarker.kind()).Count() - initial_count)

        qry = datastore.Query(UniqueMarker.kind())
        qry.Order(("created", datastore.Query.DESCENDING))

        marker = [ x for x in qry.Run()][0]
        # Make sure we assigned the instance
        self.assertEqual(marker["instance"], datastore.Key.from_path(instance._meta.db_table, instance.pk))

        expected_marker = "{}|name:{}".format(ModelWithUniques._meta.db_table, md5("One").hexdigest())
        self.assertEqual(expected_marker, marker.key().id_or_name())

        instance.name = "Two"

        from djangae.db.backends.appengine.commands import datastore as to_patch

        try:
            original = to_patch.Put

            def func(*args, **kwargs):
                kind = args[0][0].kind() if isinstance(args[0], list) else args[0].kind()

                if kind == UniqueMarker.kind():
                    return original(*args, **kwargs)

                raise AssertionError()

            to_patch.Put = func

            with self.assertRaises(Exception):
                instance.save()
        finally:
            to_patch.Put = original

        self.assertEqual(1, datastore.Query(UniqueMarker.kind()).Count() - initial_count)
        marker = [x for x in qry.Run()][0]
        # Make sure we assigned the instance
        self.assertEqual(marker["instance"], datastore.Key.from_path(instance._meta.db_table, instance.pk))

        expected_marker = "{}|name:{}".format(ModelWithUniques._meta.db_table, md5("One").hexdigest())
        self.assertEqual(expected_marker, marker.key().id_or_name())

    def test_error_on_insert_doesnt_create_markers(self):
        initial_count = datastore.Query(UniqueMarker.kind()).Count()

        from djangae.db.backends.appengine.commands import datastore as to_patch
        try:
            original = to_patch.Put

            def func(*args, **kwargs):
                kind = args[0][0].kind() if isinstance(args[0], list) else args[0].kind()

                if kind == UniqueMarker.kind():
                    return original(*args, **kwargs)

                raise AssertionError()

            to_patch.Put = func

            with self.assertRaises(AssertionError):
                ModelWithUniques.objects.create(name="One")
        finally:
            to_patch.Put = original

        self.assertEqual(0, datastore.Query(UniqueMarker.kind()).Count() - initial_count)

    def test_delete_clears_markers(self):
        initial_count = datastore.Query(UniqueMarker.kind()).Count()

        instance = ModelWithUniques.objects.create(name="One")
        self.assertEqual(1, datastore.Query(UniqueMarker.kind()).Count() - initial_count)
        instance.delete()
        self.assertEqual(0, datastore.Query(UniqueMarker.kind()).Count() - initial_count)

    @override_settings(DJANGAE_DISABLE_CONSTRAINT_CHECKS=True)
    def test_constraints_disabled_doesnt_create_or_check_markers(self):
        initial_count = datastore.Query(UniqueMarker.kind()).Count()

        instance1 = ModelWithUniques.objects.create(name="One")

        self.assertEqual(initial_count, datastore.Query(UniqueMarker.kind()).Count())

        instance2 = ModelWithUniques.objects.create(name="One")

        self.assertEqual(instance1.name, instance2.name)
        self.assertFalse(instance1 == instance2)

    @override_settings(DJANGAE_DISABLE_CONSTRAINT_CHECKS=True)
    def test_constraints_can_be_enabled_per_model(self):

        initial_count = datastore.Query(UniqueMarker.kind()).Count()
        ModelWithUniquesAndOverride.objects.create(name="One")

        self.assertEqual(1, datastore.Query(UniqueMarker.kind()).Count() - initial_count)

    def test_list_field_unique_constaints(self):
        instance1 = UniqueModel.objects.create(unique_field=1, unique_combo_one=1, unique_list_field=["A", "C"])

        with self.assertRaises((IntegrityError, DataError)):
            UniqueModel.objects.create(unique_field=2, unique_combo_one=2, unique_list_field=["A"])

        instance2 = UniqueModel.objects.create(unique_field=2, unique_combo_one=2, unique_list_field=["B"])

        instance2.unique_list_field = instance1.unique_list_field

        with self.assertRaises((IntegrityError, DataError)):
            instance2.save()

        instance1.unique_list_field = []
        instance1.save()

        instance2.save()

    def test_list_field_unique_constraints_validation(self):
        instance1 = UniqueModel(
            unique_set_field={"A"},
            unique_together_list_field=[1],
            unique_field=1,
            unique_combo_one=1,
            unique_list_field=["A", "C"]
        )

        # Without a custom mixin, Django can't construct a unique validation query for a list field
        self.assertRaises(BadValueError, instance1.full_clean)
        UniqueModel.__bases__ = (UniquenessMixin,) + UniqueModel.__bases__
        instance1.full_clean()
        instance1.save()

        # Check the uniqueness mixing works with long lists
        instance1.unique_list_field = [ x for x in range(31) ]
        try:
            instance1.full_clean()
        except NotSupportedError:
            self.fail("Couldn't run unique check on long list field")
            return

        instance2 = UniqueModel(
            unique_set_field={"B"},
            unique_together_list_field=[2],
            unique_field=2,
            unique_combo_one=2,
            unique_list_field=["B", "C"]  # duplicate value C!
        )

        self.assertRaises(ValidationError, instance2.full_clean)
        UniqueModel.__bases__ = (models.Model,)

    def test_set_field_unique_constraints(self):
        instance1 = UniqueModel.objects.create(unique_field=1, unique_combo_one=1, unique_set_field={"A", "C"})

        with self.assertRaises((IntegrityError, DataError)):
            UniqueModel.objects.create(unique_field=2, unique_combo_one=2, unique_set_field={"A"})

        instance2 = UniqueModel.objects.create(unique_field=2, unique_combo_one=2, unique_set_field={"B"})

        instance2.unique_set_field = instance1.unique_set_field

        with self.assertRaises((IntegrityError, DataError)):
            instance2.save()

        instance1.unique_set_field = set()
        instance1.save()

        instance2.save()

        instance2.unique_set_field = set()
        instance2.save() # You can have two fields with empty sets

    def test_unique_constraints_on_model_with_long_str_pk(self):
        """ Check that an object with a string-based PK of 500 characters (the max that GAE allows)
            can still have unique constraints pointing at it.  (See #242.)
        """
        obj = UniqueModelWithLongPK(pk="x" * 500, unique_field=1)
        obj.save()
        duplicate = UniqueModelWithLongPK(pk="y" * 500, unique_field=1)
        self.assertRaises(IntegrityError, duplicate.save)


class EdgeCaseTests(TestCase):
    def setUp(self):
        super(EdgeCaseTests, self).setUp()

        add_special_index(TestUser, "username", "iexact")

        self.u1 = TestUser.objects.create(username="A", email="test@example.com", last_login=datetime.datetime.now().date(), id=1)
        self.u2 = TestUser.objects.create(username="B", email="test@example.com", last_login=datetime.datetime.now().date(), id=2)
        self.u3 = TestUser.objects.create(username="C", email="test2@example.com", last_login=datetime.datetime.now().date(), id=3)
        self.u4 = TestUser.objects.create(username="D", email="test3@example.com", last_login=datetime.datetime.now().date(), id=4)
        self.u5 = TestUser.objects.create(username="E", email="test3@example.com", last_login=datetime.datetime.now().date(), id=5)

        self.apple = TestFruit.objects.create(name="apple", color="red")
        self.banana = TestFruit.objects.create(name="banana", color="yellow")

    def test_querying_by_date(self):
        instance1 = ModelWithDates.objects.create(start=datetime.date(2014, 1, 1), end=datetime.date(2014, 1, 20))
        instance2 = ModelWithDates.objects.create(start=datetime.date(2014, 2, 1), end=datetime.date(2014, 2, 20))

        self.assertEqual(instance1, ModelWithDates.objects.get(start__lt=datetime.date(2014, 1, 2)))
        self.assertEqual(2, ModelWithDates.objects.filter(start__lt=datetime.date(2015, 1, 1)).count())

        self.assertEqual(instance2, ModelWithDates.objects.get(start__gt=datetime.date(2014, 1, 2)))
        self.assertEqual(instance2, ModelWithDates.objects.get(start__gte=datetime.date(2014, 2, 1)))

    def test_double_starts_with(self):
        qs = TestUser.objects.filter(username__startswith='Hello') |  TestUser.objects.filter(username__startswith='Goodbye')

        self.assertEqual(0, qs.count())

        TestUser.objects.create(username="Hello")
        self.assertEqual(1, qs.count())

        TestUser.objects.create(username="Goodbye")
        self.assertEqual(2, qs.count())

        TestUser.objects.create(username="Hello and Goodbye")
        self.assertEqual(3, qs.count())

    def test_impossible_starts_with(self):
        TestUser.objects.create(username="Hello")
        TestUser.objects.create(username="Goodbye")
        TestUser.objects.create(username="Hello and Goodbye")

        qs = TestUser.objects.filter(username__startswith='Hello') &  TestUser.objects.filter(username__startswith='Goodbye')
        self.assertEqual(0, qs.count())

    def test_datetime_contains(self):
        """
            Django allows for __contains on datetime field, so that you can search for a specific
            date. This is probably just because SQL allows querying it on a string, and contains just
            turns into a like query. This test just makes sure we behave the same
        """

        instance = DateTimeModel.objects.create() # Create a DateTimeModel, it has auto_now stuff

        # Make sure that if we query a datetime on a date it is properly returned
        self.assertItemsEqual([instance], DateTimeModel.objects.filter(datetime_field__contains=instance.datetime_field.date()))
        self.assertItemsEqual([instance], DateTimeModel.objects.filter(date_field__contains=instance.date_field.year))

    def test_combinations_of_special_indexes(self):
        qs = TestUser.objects.filter(username__iexact='Hello') | TestUser.objects.filter(username__contains='ood')

        self.assertEqual(0, qs.count())

        TestUser.objects.create(username="Hello")
        self.assertEqual(1, qs.count())

        TestUser.objects.create(username="Goodbye")
        self.assertEqual(2, qs.count())

        TestUser.objects.create(username="Hello and Goodbye")
        self.assertEqual(3, qs.count())

    def test_multi_table_inheritance(self):

        parent = MultiTableParent.objects.create(parent_field="parent1")
        child1 = MultiTableChildOne.objects.create(parent_field="child1", child_one_field="child1")
        child2 = MultiTableChildTwo.objects.create(parent_field="child2", child_two_field="child2")

        self.assertEqual(3, MultiTableParent.objects.count())
        self.assertItemsEqual([parent.pk, child1.pk, child2.pk],
            list(MultiTableParent.objects.values_list('pk', flat=True)))
        self.assertEqual(1, MultiTableChildOne.objects.count())
        self.assertEqual(child1, MultiTableChildOne.objects.get())

        self.assertEqual(1, MultiTableChildTwo.objects.count())
        self.assertEqual(child2, MultiTableChildTwo.objects.get())

        self.assertEqual(child2, MultiTableChildTwo.objects.get(pk=child2.pk))
        self.assertTrue(MultiTableParent.objects.filter(pk=child2.pk).exists())

    def test_anding_pks(self):
        results = TestUser.objects.filter(id__exact=self.u1.pk).filter(id__exact=self.u2.pk)
        self.assertEqual(list(results), [])

    def test_unusual_queries(self):

        results = TestFruit.objects.filter(name__in=["apple", "orange"])
        self.assertEqual(1, len(results))
        self.assertItemsEqual(["apple"], [x.name for x in results])

        results = TestFruit.objects.filter(name__in=["apple", "banana"])
        self.assertEqual(2, len(results))
        self.assertItemsEqual(["apple", "banana"], [x.name for x in results])

        results = TestFruit.objects.filter(name__in=["apple", "banana"]).values_list('pk', 'color')
        self.assertEqual(2, len(results))
        self.assertItemsEqual([(self.apple.pk, self.apple.color), (self.banana.pk, self.banana.color)], results)

        results = TestUser.objects.all()
        self.assertEqual(5, len(results))

        results = TestUser.objects.filter(username__in=["A", "B"])
        self.assertEqual(2, len(results))
        self.assertItemsEqual(["A", "B"], [x.username for x in results])

        results = TestUser.objects.filter(username__in=["A", "B"]).exclude(username="A")
        self.assertEqual(1, len(results), results)
        self.assertItemsEqual(["B"], [x.username for x in results])

        results = TestUser.objects.filter(username__lt="E")
        self.assertEqual(4, len(results))
        self.assertItemsEqual(["A", "B", "C", "D"], [x.username for x in results])

        results = TestUser.objects.filter(username__lte="E")
        self.assertEqual(5, len(results))

        #Double exclude on different properties not supported
        with self.assertRaises(NotSupportedError):
            #FIXME: This should raise a NotSupportedError, but at the moment it's thrown too late in
            #the process and so Django wraps it as a DataError
            list(TestUser.objects.exclude(username="E").exclude(email="A"))

        results = list(TestUser.objects.exclude(username="E").exclude(username="A"))
        self.assertItemsEqual(["B", "C", "D"], [x.username for x in results ])

        results = TestUser.objects.filter(username="A", email="test@example.com")
        self.assertEqual(1, len(results))

        results = TestUser.objects.filter(username__in=["A", "B"]).filter(username__in=["A", "B"])
        self.assertEqual(2, len(results))
        self.assertItemsEqual(["A", "B"], [x.username for x in results])

        results = TestUser.objects.filter(username__in=["A", "B"]).filter(username__in=["A"])
        self.assertEqual(1, len(results))
        self.assertItemsEqual(["A"], [x.username for x in results])

        results = TestUser.objects.filter(pk__in=[self.u1.pk, self.u2.pk]).filter(username__in=["A"])
        self.assertEqual(1, len(results))
        self.assertItemsEqual(["A"], [x.username for x in results])

        results = TestUser.objects.filter(username__in=["A"]).filter(pk__in=[self.u1.pk, self.u2.pk])
        self.assertEqual(1, len(results))
        self.assertItemsEqual(["A"], [x.username for x in results])

        results = list(TestUser.objects.all().exclude(username__in=["A"]))
        self.assertItemsEqual(["B", "C", "D", "E"], [x.username for x in results ])

        results = list(TestFruit.objects.filter(name='apple', color__in=[]))
        self.assertItemsEqual([], results)

        results = list(TestUser.objects.all().exclude(username__in=[]))
        self.assertEqual(5, len(results))
        self.assertItemsEqual(["A", "B", "C", "D", "E"], [x.username for x in results ])

        results = list(TestUser.objects.all().exclude(username__in=[]).filter(username__in=["A", "B"]))
        self.assertEqual(2, len(results))
        self.assertItemsEqual(["A", "B"], [x.username for x in results])

        results = list(TestUser.objects.all().filter(username__in=["A", "B"]).exclude(username__in=[]))
        self.assertEqual(2, len(results))
        self.assertItemsEqual(["A", "B"], [x.username for x in results])

    def test_empty_string_key(self):
        # Creating
        with self.assertRaises(IntegrityError):
            TestFruit.objects.create(name='')

        # Getting
        with self.assertRaises(TestFruit.DoesNotExist):
            TestFruit.objects.get(name='')

        # Filtering
        results = list(TestFruit.objects.filter(name=''))
        self.assertItemsEqual([], results)

        # Combined filtering
        results = list(TestFruit.objects.filter(name='', color='red'))
        self.assertItemsEqual([], results)

        # IN query
        results = list(TestFruit.objects.filter(name__in=['', 'apple']))
        self.assertItemsEqual([self.apple], results)

    def test_or_queryset(self):
        """
            This constructs an OR query, this is currently broken in the parse_where_and_check_projection
            function. WE MUST FIX THIS!
        """
        q1 = TestUser.objects.filter(username="A")
        q2 = TestUser.objects.filter(username="B")

        self.assertItemsEqual([self.u1, self.u2], list(q1 | q2))

    def test_or_q_objects(self):
        """ Test use of Q objects in filters. """
        query = TestUser.objects.filter(Q(username="A") | Q(username="B"))
        self.assertItemsEqual([self.u1, self.u2], list(query))

    def test_extra_select(self):
        results = TestUser.objects.filter(username='A').extra(select={'is_a': "username = 'A'"})
        self.assertEqual(1, len(results))
        self.assertItemsEqual([True], [x.is_a for x in results])

        results = TestUser.objects.all().exclude(username='A').extra(select={'is_a': "username = 'A'"})
        self.assertEqual(4, len(results))
        self.assertEqual(not any([x.is_a for x in results]), True)

        # Up for debate
        # results = User.objects.all().extra(select={'truthy': 'TRUE'})
        # self.assertEqual(all([x.truthy for x in results]), True)

        results = TestUser.objects.all().extra(select={'truthy': True})
        self.assertEqual(all([x.truthy for x in results]), True)

    def test_counts(self):
        self.assertEqual(5, TestUser.objects.count())
        self.assertEqual(2, TestUser.objects.filter(email="test3@example.com").count())
        self.assertEqual(3, TestUser.objects.exclude(email="test3@example.com").count())
        self.assertEqual(1, TestUser.objects.filter(username="A").exclude(email="test3@example.com").count())
        self.assertEqual(3, TestUser.objects.exclude(username="E").exclude(username="A").count())

    def test_deletion(self):
        count = TestUser.objects.count()
        self.assertTrue(count)

        TestUser.objects.filter(username="A").delete()
        self.assertEqual(count - 1, TestUser.objects.count())

        TestUser.objects.filter(username="B").exclude(username="B").delete() #Should do nothing
        self.assertEqual(count - 1, TestUser.objects.count())

        TestUser.objects.all().delete()
        count = TestUser.objects.count()
        self.assertFalse(count)

    def test_insert_with_existing_key(self):
        user = TestUser.objects.create(id=999, username="test1", last_login=datetime.datetime.now().date())
        self.assertEqual(999, user.pk)

        with self.assertRaises(IntegrityError):
            TestUser.objects.create(id=999, username="test2", last_login=datetime.datetime.now().date())

    def test_included_pks(self):
        ids = [ TestUser.objects.get(username="B").pk, TestUser.objects.get(username="A").pk ]
        results = TestUser.objects.filter(pk__in=ids).order_by("username")

        self.assertEqual(results[0], self.u1)
        self.assertEqual(results[1], self.u2)

    def test_select_related(self):
        """ select_related should be a no-op... for now """
        user = TestUser.objects.get(username="A")
        Permission.objects.create(user=user, perm="test_perm")
        select_related = [ (p.perm, p.user.username) for p in user.permission_set.select_related() ]
        self.assertEqual(user.username, select_related[0][1])

    def test_cross_selects(self):
        user = TestUser.objects.get(username="A")
        Permission.objects.create(user=user, perm="test_perm")
        with self.assertRaises(NotSupportedError):
            perms = list(Permission.objects.all().values_list("user__username", "perm"))
            self.assertEqual("A", perms[0][0])

    def test_values_list_on_pk_does_keys_only_query(self):
        from google.appengine.api.datastore import Query

        def replacement_init(*args, **kwargs):
            replacement_init.called_args = args
            replacement_init.called_kwargs = kwargs
            original_init(*args, **kwargs)

        replacement_init.called_args = None
        replacement_init.called_kwargs = None

        try:
            original_init = Query.__init__
            Query.__init__ = replacement_init
            list(TestUser.objects.all().values_list('pk', flat=True))
        finally:
            Query.__init__ = original_init

        self.assertTrue(replacement_init.called_kwargs.get('keys_only'))
        self.assertEqual(5, len(TestUser.objects.all().values_list('pk')))

    def test_iexact(self):
        user = TestUser.objects.get(username__iexact="a")
        self.assertEqual("A", user.username)

        add_special_index(IntegerModel, "integer_field", "iexact")
        IntegerModel.objects.create(integer_field=1000)
        integer_model = IntegerModel.objects.get(integer_field__iexact=str(1000))
        self.assertEqual(integer_model.integer_field, 1000)

        user = TestUser.objects.get(id__iexact=str(self.u1.id))
        self.assertEqual("A", user.username)

    def test_ordering(self):
        users = TestUser.objects.all().order_by("username")

        self.assertEqual(["A", "B", "C", "D", "E"], [x.username for x in users])

        users = TestUser.objects.all().order_by("-username")

        self.assertEqual(["A", "B", "C", "D", "E"][::-1], [x.username for x in users])

        with self.assertRaises(FieldError):
            users = list(TestUser.objects.order_by("bananas"))

        users = TestUser.objects.filter(id__in=[self.u2.id, self.u3.id, self.u4.id]).order_by('id')
        self.assertEqual(["B", "C", "D"], [x.username for x in users])

        users = TestUser.objects.filter(id__in=[self.u2.id, self.u3.id, self.u4.id]).order_by('-id')
        self.assertEqual(["D", "C", "B"], [x.username for x in users])

        users = TestUser.objects.filter(id__in=[self.u1.id, self.u5.id, self.u3.id]).order_by('id')
        self.assertEqual(["A", "C", "E"], [x.username for x in users])

        users = TestUser.objects.filter(id__in=[self.u4.id, self.u5.id, self.u3.id, self.u1.id]).order_by('-id')
        self.assertEqual(["E", "D", "C", "A"], [x.username for x in users])

    def test_dates_query(self):
        z_user = TestUser.objects.create(username="Z", email="z@example.com")
        z_user.last_login = datetime.date(2013, 4, 5)
        z_user.save()

        last_a_login = TestUser.objects.get(username="A").last_login

        dates = TestUser.objects.dates('last_login', 'year')

        self.assertItemsEqual(
            [datetime.date(2013, 1, 1), datetime.date(last_a_login.year, 1, 1)],
            dates
        )

        dates = TestUser.objects.dates('last_login', 'month')
        self.assertItemsEqual(
            [datetime.date(2013, 4, 1), datetime.date(last_a_login.year, last_a_login.month, 1)],
            dates
        )

        dates = TestUser.objects.dates('last_login', 'day')
        self.assertItemsEqual(
            [datetime.date(2013, 4, 5), last_a_login],
            dates
        )

        dates = TestUser.objects.dates('last_login', 'day', order='DESC')
        self.assertItemsEqual(
            [last_a_login, datetime.date(2013, 4, 5)],
            dates
        )

    def test_in_query(self):
        """ Test that the __in filter works, and that it cannot be used with more than 30 values,
            unless it's used on the PK field.
        """
        # Check that a basic __in query works
        results = list(TestUser.objects.filter(username__in=['A', 'B']))
        self.assertItemsEqual(results, [self.u1, self.u2])
        # Check that it also works on PKs
        results = list(TestUser.objects.filter(pk__in=[self.u1.pk, self.u2.pk]))
        self.assertItemsEqual(results, [self.u1, self.u2])
        # Check that using more than 30 items in an __in query not on the pk causes death
        query = TestUser.objects.filter(username__in=list([x for x in letters[:31]]))
        # This currently raises an error from App Engine, should we raise our own?
        self.assertRaises(Exception, list, query)
        # Check that it's ok with PKs though
        query = TestUser.objects.filter(pk__in=list(xrange(1, 32)))
        list(query)

    def test_self_relations(self):
        obj = SelfRelatedModel.objects.create()
        obj2 = SelfRelatedModel.objects.create(related=obj)
        self.assertEqual(list(obj.selfrelatedmodel_set.all()), [obj2])

    def test_special_indexes_for_empty_fields(self):
        obj = TestFruit.objects.create(name='pear')
        indexes = ['icontains', 'contains', 'iexact', 'iendswith', 'endswith', 'istartswith', 'startswith']
        for index in indexes:
            add_special_index(TestFruit, 'color', index)
        obj.save()

    def test_special_indexes_for_unusually_long_values(self):
        obj = TestFruit.objects.create(name='pear', color='1234567890-=!@#$%^&*()_+qQWERwertyuiopasdfghjklzxcvbnm')
        indexes = ['icontains', 'contains', 'iexact', 'iendswith', 'endswith', 'istartswith', 'startswith']
        for index in indexes:
            add_special_index(TestFruit, 'color', index)
        obj.save()

        qry = TestFruit.objects.filter(color__contains='1234567890-=!@#$%^&*()_+qQWERwertyuiopasdfghjklzxcvbnm')
        self.assertEqual(len(list(qry)), 1)
        qry = TestFruit.objects.filter(color__contains='890-=!@#$')
        self.assertEqual(len(list(qry)), 1)
        qry = TestFruit.objects.filter(color__contains='1234567890-=!@#$%^&*()_+qQWERwertyui')
        self.assertEqual(len(list(qry)), 1)
        qry = TestFruit.objects.filter(color__contains='8901')
        self.assertEqual(len(list(qry)), 0)

        qry = TestFruit.objects.filter(color__icontains='1234567890-=!@#$%^&*()_+qQWERWERTYuiopasdfghjklzxcvbnm')
        self.assertEqual(len(list(qry)), 1)
        qry = TestFruit.objects.filter(color__icontains='890-=!@#$')
        self.assertEqual(len(list(qry)), 1)
        qry = TestFruit.objects.filter(color__icontains='1234567890-=!@#$%^&*()_+qQWERwertyuI')
        self.assertEqual(len(list(qry)), 1)
        qry = TestFruit.objects.filter(color__icontains='8901')
        self.assertEqual(len(list(qry)), 0)



class BlobstoreFileUploadHandlerTest(TestCase):
    boundary = "===============7417945581544019063=="

    def setUp(self):
        super(BlobstoreFileUploadHandlerTest, self).setUp()

        self.request = RequestFactory().get('/')
        self.request.META = {
            'wsgi.input': self._create_wsgi_input(),
            'content-type': 'message/external-body; blob-key="PLOF0qOie14jzHWJXEa9HA=="; access-type="X-AppEngine-BlobKey"'
        }
        self.uploader = BlobstoreFileUploadHandler(self.request)

    def _create_wsgi_input(self):
        return StringIO('--===============7417945581544019063==\r\nContent-Type:'
                        ' text/plain\r\nContent-Disposition: form-data;'
                        ' name="field-nationality"\r\n\r\nAS\r\n'
                        '--===============7417945581544019063==\r\nContent-Type:'
                        ' message/external-body; blob-key="PLOF0qOie14jzHWJXEa9HA==";'
                        ' access-type="X-AppEngine-BlobKey"\r\nContent-Disposition:'
                        ' form-data; name="field-file";'
                        ' filename="Scan.tiff"\r\n\r\nContent-Type: image/tiff'
                        '\r\nContent-Length: 19837164\r\nContent-MD5:'
                        ' YjI1M2Q5NjM5YzdlMzUxYjMyMjA0ZTIxZjAyNzdiM2Q=\r\ncontent-disposition:'
                        ' form-data; name="field-file";'
                        ' filename="Scan.tiff"\r\nX-AppEngine-Upload-Creation: 2014-03-07'
                        ' 14:48:03.246607\r\n\r\n\r\n'
                        '--===============7417945581544019063==\r\nContent-Type:'
                        ' text/plain\r\nContent-Disposition: form-data;'
                        ' name="field-number"\r\n\r\n6\r\n'
                        '--===============7417945581544019063==\r\nContent-Type:'
                        ' text/plain\r\nContent-Disposition: form-data;'
                        ' name="field-salutation"\r\n\r\nmrs\r\n'
                        '--===============7417945581544019063==--')

    def test_non_existing_files_do_not_get_created(self):
        file_field_name = 'field-file'
        length = len(self._create_wsgi_input().read())
        self.uploader.handle_raw_input(self.request.META['wsgi.input'], self.request.META, length, self.boundary, "utf-8")
        self.assertRaises(StopFutureHandlers, self.uploader.new_file, file_field_name, 'file_name', None, None)
        self.assertRaises(EntityNotFoundError, self.uploader.file_complete, None)

    def test_blob_key_creation(self):
        file_field_name = 'field-file'
        length = len(self._create_wsgi_input().read())
        self.uploader.handle_raw_input(self.request.META['wsgi.input'], self.request.META, length, self.boundary, "utf-8")
        self.assertRaises(
            StopFutureHandlers,
            self.uploader.new_file, file_field_name, 'file_name', None, None
        )
        self.assertIsNotNone(self.uploader.blobkey)

    def test_blobstore_upload_url_templatetag(self):
        template = """{% load storage %}{% blobstore_upload_url '/something/' %}"""
        response = Template(template).render(Context({}))
        self.assertTrue(response.startswith("http://localhost:8080/_ah/upload/"))


class ApplicationTests(TestCase):

    @unittest.skipIf(webtest is NotImplemented, "pip install webtest to run functional tests")
    def test_environ_is_patched_when_request_processed(self):
        def application(environ, start_response):
            # As we're not going through a thread pool the environ is unset.
            # Set it up manually here.
            # TODO: Find a way to get it to be auto-set by webtest
            from google.appengine.runtime import request_environment
            request_environment.current_request.environ = environ

            # Check if the os.environ is the same as what we expect from our
            # wsgi environ
            import os
            self.assertEqual(environ, os.environ)
            start_response("200 OK", [])
            return ["OK"]

        djangae_app = DjangaeApplication(application)
        test_app = webtest.TestApp(djangae_app)
        old_environ = os.environ
        try:
            test_app.get("/")
        finally:
            os.environ = old_environ


class ComputedFieldModel(models.Model):
    def computer(self):
        return "%s_%s" % (self.int_field, self.char_field)

    int_field = models.IntegerField()
    char_field = models.CharField(max_length=50)
    test_field = ComputedCharField(computer, max_length=50)

    class Meta:
        app_label = "djangae"


class ComputedFieldTests(TestCase):
    def test_computed_field(self):
        instance = ComputedFieldModel(int_field=1, char_field="test")
        instance.save()
        self.assertEqual(instance.test_field, "1_test")

        # Try getting and saving the instance again
        instance = ComputedFieldModel.objects.get(test_field="1_test")
        instance.save()


class ModelWithCounter(models.Model):
    counter = ShardedCounterField()


class ShardedCounterTest(TestCase):
    def test_basic_usage(self):
        instance = ModelWithCounter.objects.create()

        self.assertEqual(0, instance.counter.value())

        instance.counter.increment()

        self.assertEqual(30, len(instance.counter))
        self.assertEqual(30, CounterShard.objects.count())
        self.assertEqual(1, instance.counter.value())

        instance.counter.increment()
        self.assertEqual(2, instance.counter.value())

        instance.counter.decrement()
        self.assertEqual(1, instance.counter.value())

        instance.counter.decrement()

        self.assertEqual(0, instance.counter.value())

        instance.counter.decrement()
        self.assertEqual(0, instance.counter.value())


class IterableFieldTests(TestCase):
    def test_filtering_on_iterable_fields(self):
        list1 = IterableFieldModel.objects.create(
            list_field=['A', 'B', 'C', 'D', 'E', 'F', 'G'],
            set_field=set(['A', 'B', 'C', 'D', 'E', 'F', 'G']))
        list2 = IterableFieldModel.objects.create(
            list_field=['A', 'B', 'C', 'H', 'I', 'J'],
            set_field=set(['A', 'B', 'C', 'H', 'I', 'J']))

        # filtering using exact lookup with ListField:
        qry = IterableFieldModel.objects.filter(list_field='A')
        self.assertEqual(sorted(x.pk for x in qry), sorted([list1.pk, list2.pk]))
        qry = IterableFieldModel.objects.filter(list_field='H')
        self.assertEqual(sorted(x.pk for x in qry), [list2.pk,])

        # filtering using exact lookup with SetField:
        qry = IterableFieldModel.objects.filter(set_field='A')
        self.assertEqual(sorted(x.pk for x in qry), sorted([list1.pk, list2.pk]))
        qry = IterableFieldModel.objects.filter(set_field='H')
        self.assertEqual(sorted(x.pk for x in qry), [list2.pk,])

        # filtering using in lookup with ListField:
        qry = IterableFieldModel.objects.filter(list_field__in=['A', 'B', 'C'])
        self.assertEqual(sorted(x.pk for x in qry), sorted([list1.pk, list2.pk,]))
        qry = IterableFieldModel.objects.filter(list_field__in=['H', 'I', 'J'])
        self.assertEqual(sorted(x.pk for x in qry), sorted([list2.pk,]))

        # filtering using in lookup with SetField:
        qry = IterableFieldModel.objects.filter(set_field__in=set(['A', 'B']))
        self.assertEqual(sorted(x.pk for x in qry), sorted([list1.pk, list2.pk]))
        qry = IterableFieldModel.objects.filter(set_field__in=set(['H']))
        self.assertEqual(sorted(x.pk for x in qry), [list2.pk,])

    def test_empty_iterable_fields(self):
        """ Test that an empty set field always returns set(), not None """
        instance = IterableFieldModel()
        # When assigning
        self.assertEqual(instance.set_field, set())
        self.assertEqual(instance.list_field, [])
        instance.save()

        instance = IterableFieldModel.objects.get()
        # When getting it from the db
        self.assertEqual(instance.set_field, set())
        self.assertEqual(instance.list_field, [])

    def test_list_field(self):
        instance = IterableFieldModel.objects.create()
        self.assertEqual([], instance.list_field)
        instance.list_field.append("One")
        self.assertEqual(["One"], instance.list_field)
        instance.save()

        self.assertEqual(["One"], instance.list_field)

        instance = IterableFieldModel.objects.get(pk=instance.pk)
        self.assertEqual(["One"], instance.list_field)

        instance.list_field = None

        # Or anything else for that matter!
        with self.assertRaises(ValueError):
            instance.list_field = "Bananas"
            instance.save()

        results = IterableFieldModel.objects.filter(list_field="One")
        self.assertEqual([instance], list(results))

    def test_set_field(self):
        instance = IterableFieldModel.objects.create()
        self.assertEqual(set(), instance.set_field)
        instance.set_field.add("One")
        self.assertEqual(set(["One"]), instance.set_field)
        instance.save()

        self.assertEqual(set(["One"]), instance.set_field)

        instance = IterableFieldModel.objects.get(pk=instance.pk)
        self.assertEqual(set(["One"]), instance.set_field)

        instance.set_field = None

        # Or anything else for that matter!
        with self.assertRaises(ValueError):
            instance.set_field = "Bananas"
            instance.save()

    def test_empty_list_queryable_with_is_null(self):
        instance = IterableFieldModel.objects.create()

        self.assertTrue(IterableFieldModel.objects.filter(set_field__isnull=True).exists())

        instance.set_field.add(1)
        instance.save()

        self.assertFalse(IterableFieldModel.objects.filter(set_field__isnull=True).exists())
        self.assertTrue(IterableFieldModel.objects.filter(set_field__isnull=False).exists())

        self.assertFalse(IterableFieldModel.objects.exclude(set_field__isnull=False).exists())
        self.assertTrue(IterableFieldModel.objects.exclude(set_field__isnull=True).exists())


class InstanceSetFieldTests(TestCase):

    def test_deserialization(self):
        i1 = ISOther.objects.create(pk=1)
        i2 = ISOther.objects.create(pk=2)

        self.assertEqual(set([i1, i2]), ISModel._meta.get_field("related_things").to_python("[1, 2]"))

    def test_basic_usage(self):
        main = ISModel.objects.create()
        other = ISOther.objects.create(name="test")
        other2 = ISOther.objects.create(name="test2")

        main.related_things.add(other)
        main.save()

        self.assertEqual({other.pk}, main.related_things_ids)
        self.assertEqual(list(ISOther.objects.filter(pk__in=main.related_things_ids)), list(main.related_things.all()))

        self.assertEqual([main], list(other.ismodel_set.all()))

        main.related_things.remove(other)
        self.assertFalse(main.related_things_ids)

        main.related_things = {other2}
        self.assertEqual({other2.pk}, main.related_things_ids)

        with self.assertRaises(AttributeError):
            other.ismodel_set = {main}

        without_reverse = RelationWithoutReverse.objects.create(name="test3")
        self.assertFalse(hasattr(without_reverse, "ismodel_set"))

    def test_save_and_load_empty(self):
        """
        Create a main object with no related items,
        get a copy of it back from the db and try to read items.
        """
        main = ISModel.objects.create()
        main_from_db = ISModel.objects.get(pk=main.pk)

        # Fetch the container from the database and read its items
        self.assertItemsEqual(main_from_db.related_things.all(), [])

    def test_add_to_empty(self):
        """
        Create a main object with no related items,
        get a copy of it back from the db and try to add items.
        """
        main = ISModel.objects.create()
        main_from_db = ISModel.objects.get(pk=main.pk)

        other = ISOther.objects.create()
        main_from_db.related_things.add(other)
        main_from_db.save()

    def test_add_another(self):
        """
        Create a main object with related items,
        get a copy of it back from the db and try to add more.
        """
        main = ISModel.objects.create()
        other1 = ISOther.objects.create()
        main.related_things.add(other1)
        main.save()

        main_from_db = ISModel.objects.get(pk=main.pk)
        other2 = ISOther.objects.create()

        main_from_db.related_things.add(other2)
        main_from_db.save()

    def test_multiple_objects(self):
        main = ISModel.objects.create()
        other1 = ISOther.objects.create()
        other2 = ISOther.objects.create()

        main.related_things.add(other1, other2)
        main.save()

        main_from_db = ISModel.objects.get(pk=main.pk)
        self.assertEqual(main_from_db.related_things.count(), 2)

    def test_deletion(self):
        """
        Delete one of the objects referred to by the related field
        """
        main = ISModel.objects.create()
        other = ISOther.objects.create()
        main.related_things.add(other)
        main.save()

        other.delete()
        self.assertEqual(main.related_things.count(), 0)


class TestGenericRelationField(TestCase):
    def test_basic_usage(self):
        instance = GenericRelationModel.objects.create()
        self.assertIsNone(instance.relation_to_content_type)

        ct = ContentType.objects.create()
        instance.relation_to_content_type = ct
        instance.save()

        self.assertTrue(instance.relation_to_content_type_id)

        instance = GenericRelationModel.objects.get()
        self.assertEqual(ct, instance.relation_to_content_type)

    def test_overridden_dbtable(self):
        instance = GenericRelationModel.objects.create()
        self.assertIsNone(instance.relation_to_weird)

        ct = ContentType.objects.create()
        instance.relation_to_weird = ct
        instance.save()

        self.assertTrue(instance.relation_to_weird_id)

        instance = GenericRelationModel.objects.get()
        self.assertEqual(ct, instance.relation_to_weird)


class DatastorePaginatorTest(TestCase):

    def setUp(self):
        super(DatastorePaginatorTest, self).setUp()

        for i in range(15):
            PaginatorModel.objects.create(foo=i)

    def test_basic_usage(self):
        def qs():
            return PaginatorModel.objects.all().order_by('foo')

        p1 = paginator.DatastorePaginator(qs(), 5).page(1)
        self.assertFalse(p1.has_previous())
        self.assertTrue(p1.has_next())
        self.assertEqual(p1.start_index(), 1)
        self.assertEqual(p1.end_index(), 5)
        self.assertEqual(p1.next_page_number(), 2)
        self.assertEqual([x.foo for x in p1], [0, 1, 2, 3, 4])

        p2 = paginator.DatastorePaginator(qs(), 5).page(2)
        self.assertTrue(p2.has_previous())
        self.assertTrue(p2.has_next())
        self.assertEqual(p2.start_index(), 6)
        self.assertEqual(p2.end_index(), 10)
        self.assertEqual(p2.previous_page_number(), 1)
        self.assertEqual(p2.next_page_number(), 3)
        self.assertEqual([x.foo for x in p2], [5, 6, 7, 8, 9])

        p3 = paginator.DatastorePaginator(qs(), 5).page(3)
        self.assertTrue(p3.has_previous())
        self.assertFalse(p3.has_next())
        self.assertEqual(p3.start_index(), 11)
        self.assertEqual(p3.end_index(), 15)
        self.assertEqual(p3.previous_page_number(), 2)
        self.assertEqual([x.foo for x in p3], [10, 11, 12, 13, 14])

    def test_empty(self):
        qs = PaginatorModel.objects.none()
        p1 = paginator.DatastorePaginator(qs, 5).page(1)
        self.assertFalse(p1.has_previous())
        self.assertFalse(p1.has_next())
        self.assertEqual(p1.start_index(), 0)
        self.assertEqual(p1.end_index(), 0)
        self.assertEqual([x for x in p1], [])


class TestSpecialIndexers(TestCase):

    def setUp(self):
        super(TestSpecialIndexers, self).setUp()

        self.names = ['Ola', 'Adam', 'Luke', 'rob', 'Daniel', 'Ela', 'Olga', 'olek', 'ola', 'Olaaa', 'OlaaA']
        for name in self.names:
            SpecialIndexesModel.objects.create(name=name)

        self.qry = SpecialIndexesModel.objects.all()

    def test_iexact_lookup(self):
        for name in self.names:
            qry = self.qry.filter(name__iexact=name)
            self.assertEqual(len(qry), len([x for x in self.names if x.lower() == name.lower()]))

    def test_contains_lookup_and_icontains_lookup(self):
        tests = self.names + ['o', 'O', 'la']
        for name in tests:
            qry = self.qry.filter(name__contains=name)
            self.assertEqual(len(qry), len([x for x in self.names if name in x]))

            qry = self.qry.filter(name__icontains=name)
            self.assertEqual(len(qry), len([x for x in self.names if name.lower() in x.lower()]))

    def test_endswith_lookup_and_iendswith_lookup(self):
        tests = self.names + ['a', 'A', 'aa']
        for name in tests:
            qry = self.qry.filter(name__endswith=name)
            self.assertEqual(len(qry), len([x for x in self.names if x.endswith(name)]))

            qry = self.qry.filter(name__iendswith=name)
            self.assertEqual(len(qry), len([x for x in self.names if x.lower().endswith(name.lower())]))

    def test_startswith_lookup_and_istartswith_lookup(self):
        tests = self.names + ['O', 'o', 'ola']
        for name in tests:
            qry = self.qry.filter(name__startswith=name)
            self.assertEqual(len(qry), len([x for x in self.names if x.startswith(name)]))

            qry = self.qry.filter(name__istartswith=name)
            self.assertEqual(len(qry), len([x for x in self.names if x.lower().startswith(name.lower())]))

def deferred_func():
    pass

class TestHelperTests(TestCase):
    def test_inconsistent_db(self):
        with inconsistent_db():
            fruit = TestFruit.objects.create(name="banana")
            self.assertEqual(0, TestFruit.objects.count()) # Inconsistent query
            self.assertEqual(1, TestFruit.objects.filter(pk=fruit.pk).count()) #Consistent query

    def test_processing_tasks(self):
        from google.appengine.api import apiproxy_stub_map
        stub = apiproxy_stub_map.apiproxy.GetStub("taskqueue")
        stub._queues[None]._ConstructQueue("another") # Add a test queue
        stub._queues[None]._queue_yaml_parser = None # Make it so that the taskqueue stub doesn't reload from YAML

        self.assertNumTasksEquals(0) #No tasks

        deferred.defer(deferred_func)

        self.assertNumTasksEquals(1, queue_name='default')

        deferred.defer(deferred_func, _queue='another')

        self.assertNumTasksEquals(1, queue_name='another')

        taskqueue.add(url='/')
        self.assertNumTasksEquals(2, queue_name='default')

        self.process_task_queues()

        self.assertNumTasksEquals(0) #No tasks
