"""Imports between checked modules resolve to checked definitions."""

import os
from pathlib import Path

import pytest

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


DUP = Path(__file__).parent / "cases" / "dupclass"


@pytest.fixture(scope="module")
def dup_report():
    return check([str(DUP)], CheckOptions(cache_path=None, lean=False), root=str(DUP))


@pytest.fixture(scope="module")
def dup(dup_report):
    return {f.fn.name: f for f in dup_report.functions}


def test_same_named_classes_keep_their_own_lifecycles(dup_report):
    got = {(lc.cls, lc.status) for lc in dup_report.lifecycles}
    # via_signature is unsupported and may change a's Box
    assert got == {("Box@a_shapes", "open"), ("Box@b_shapes", "proved")}


@pytest.mark.parametrize(
    "fn,status",
    [
        ("read_a", "proved"),
        ("field_a", "proved"),
        ("read_b", "refuted"),  # proved if b's Box were a's
        ("field_b", "refuted"),
        ("build_b", "refuted"),
        ("via_signature", "unsupported"),  # Box only reaches it through a signature
        ("Box@a_shapes.get", "proved"),
        ("Box@b_shapes.get", "proved"),
    ],
)
def test_same_named_classes_in_different_files_are_distinct(dup, fn, status):
    assert dup[fn].status == status, dup[fn].problems
    if status == "refuted":
        assert all(v.replay.confirmed for v in dup[fn].verdicts if v.status == "refuted")
