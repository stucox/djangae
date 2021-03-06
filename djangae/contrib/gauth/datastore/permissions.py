from django.db.models.loading import get_apps, get_models
from django.contrib.auth import get_permission_codename


PERMISSIONS_LIST = None


def get_permission_choices():
    """
        Rather than creating permissions in the datastore which is incredibly slow (and relational)
        we just use the permission codenames, stored in a ListField.
    """

    global PERMISSIONS_LIST

    if PERMISSIONS_LIST:
        return PERMISSIONS_LIST

    from django.conf import settings

    AUTO_PERMISSIONS = getattr(settings, "AUTOGENERATED_PERMISSIONS", ('add', 'change', 'delete'))

    result = getattr(settings, "MANUAL_PERMISSIONS", [])

    for app in get_apps():
        for model in get_models(app):
            for action in AUTO_PERMISSIONS:
                opts = model._meta
                result.append((
                    '%s.%s' % (opts.app_label, get_permission_codename(action, opts)),
                    'Can %s %s' % (action, opts.verbose_name_raw)
                ))

    PERMISSIONS_LIST = sorted(result)
    return PERMISSIONS_LIST

