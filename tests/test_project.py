"""Imports between checked modules resolve to checked definitions."""

import os
from pathlib import Path

from telic.checker import CheckOptions, check
from telic.ledger import affected_files

ROOT = Path(__file__).parent / "cases" / "project"


def run(*paths):
    rep = check([str(ROOT / p) for p in paths], CheckOptions(cache_path=None, lean=False), root=str(ROOT))
    return rep, {f.fn.name: f for f in rep.functions}


def test_cross_module_calls_classes_enums_constants():
    rep, got = run("app")
    for name in ("fee", "Invoice.__init__", "Invoice.pay", "settle", "total_with_fee"):
        assert got[name].status == "proved", (name, got[name].status, got[name].problems)
    bad = got["bad_total"]  # through 'from . import models' and a module constant
    assert bad.status == "refuted" and all(v.replay.confirmed for v in bad.verdicts if v.status == "refuted")
    # modular: Invoice.__init__ says nothing about status, and telic says so
    oi = got["open_invoice"]
    assert oi.status == "open" and any("too weak" in v.replay.summary for v in oi.verdicts if v.replay)


def test_imported_modules_are_context_not_rechecked():
    rep, got = run("app/services.py")
    assert set(got) == {"settle", "total_with_fee", "bad_total", "open_invoice"}
    assert got["settle"].status == "proved" and got["settle"].context_deps


def test_importers_are_affected():
    scope = affected_files(str(ROOT), {"app/models.py"}, None)
    assert {"app/models.py", "app/services.py"} <= scope
