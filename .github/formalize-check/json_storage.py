"""Share equal immutable Lean-name values while retaining complete JSON trees."""

import json


def loads_with_shared_names(source, *args, **options):
    if args or options.get("cls") is not None or options.get("object_hook") is not None or options.get("object_pairs_hook") is not None:
        return json.loads(source, *args, **options)
    options.pop("object_hook", None)
    options.pop("object_pairs_hook", None)
    names = {}
    shared_ids = set()

    def share(value):
        if len(value) != 1:
            return value
        ((tag, pair),) = value.items()
        if tag not in ("str", "num") or not isinstance(pair, list) or len(pair) != 2:
            return value
        parent, component = pair
        if parent is not None and id(parent) not in shared_ids:
            return value
        if not (tag == "str" and isinstance(component, str) or
                tag == "num" and type(component) is int and component >= 0):
            return value
        key = (tag, id(parent), component)
        previous = names.get(key)
        if previous is not None:
            return previous
        names[key] = value
        shared_ids.add(id(value))
        return value

    return json.loads(source, *args, object_hook=share, **options)


class SharedNameJSON:
    """Delegate JSON behavior, retaining the original parser and full values."""

    loads = staticmethod(loads_with_shared_names)

    def __getattr__(self, name):
        return getattr(json, name)
