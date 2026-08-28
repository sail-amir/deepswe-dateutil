# -*- coding: utf-8 -*-
import sys
import importlib

try:
    from ._version import version as __version__
except ImportError:
    __version__ = 'unknown'

__all__ = ['easter', 'parser', 'relativedelta', 'rrule', 'tz',
           'utils', 'zoneinfo']

_PROVIDER_MODULES = {
    "tzstr_parser": "parser._parser",
    "rrulestr": "rrule",
    "tzfile": "tz",
}

_PROVIDERS = {}


def _register_provider(name, provider):
    """Register a callable supplied by a dateutil subpackage."""
    if name not in _PROVIDER_MODULES:
        raise ValueError("unknown provider: %s" % name)

    _PROVIDERS[name] = provider


def _get_provider(name):
    """Resolve a registered callable, importing its owner on first use."""
    try:
        return _PROVIDERS[name]
    except KeyError:
        try:
            module_name = _PROVIDER_MODULES[name]
        except KeyError:
            raise ValueError("unknown provider: %s" % name)

    importlib.import_module("." + module_name, __name__)

    try:
        return _PROVIDERS[name]
    except KeyError:
        raise RuntimeError("module %s did not register provider %s" %
                           (module_name, name))


def __getattr__(name):
    if name in __all__:
        return importlib.import_module("." + name, __name__)
    raise AttributeError(
        "module {!r} has not attribute {!r}".format(__name__, name)
    )


def __dir__():
    # __dir__ should include all the lazy-importable modules as well.
    return [x for x in globals() if x not in sys.modules] + __all__
