"""pytest plugin: enforce ``@`` contracts while your tests run.

    pytest -p telic.pytest_plugin

Every module under the test root that contains ``#@`` contracts is imported
with its contracts compiled in, so each test also exercises every
``@requires``/``@ensures``/``@invariant`` on the paths it executes. A broken
contract fails the test with the clause and line that failed.
"""

from __future__ import annotations

import os

from .runtime import install

_installed = False


def pytest_addoption(parser):
    group = parser.getgroup("telic")
    group.addoption("--telic-root", action="append", default=[], help="source roots whose contracts are enforced (default: rootdir)")


def pytest_configure(config):
    global _installed
    if _installed:
        return
    roots = config.getoption("telic_root") or [str(config.rootpath)]
    install([os.path.abspath(r) for r in roots])
    _installed = True
