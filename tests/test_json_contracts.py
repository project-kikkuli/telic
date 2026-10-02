"""Recursive JSON-shape contracts: a @trusted predicate over unchecked values,
unfolded one level per use, lets proofs rely on a validated payload."""

import json
from pathlib import Path

import pytest

from telic.aim import _aim_json
from telic.checker import CheckOptions, check
from telic.html import render_html
from telic.replay import call_text

from conftest import HAS_NODE

ROOT = Path(__file__).resolve().parent.parent
CASES = Path(__file__).parent / "cases" / "json"

EXPECTED = [
    ("payload.py", "valid_item", "trusted"),
    ("payload.py", "valid_order", "trusted"),
    ("payload.py", "total_quantity", "proved"),
    ("payload.py", "customer", "proved"),
    ("payload.py", "first_sku", "proved"),
    ("payload.py", "missing_field", "open"),
    ("payload.py", "overclaims", "open"),
    ("payload.py", "unvalidated", "refuted"),
    ("config.py", "total", "proved"),
    ("config.py", "label", "proved"),
    ("config.py", "section_name", "open"),
    ("config.py", "grandchildren", "open"),
    ("tree.ts", "leaves", "proved"),
    ("tree.ts", "overclaims", "refuted"),
    ("rebuilt.py", "present_is_not_null", "refuted"),
    ("rebuilt.py", "contains", "refuted"),
    ("rebuilt.py", "adds", "refuted"),
    ("rebuilt.py", "reads", "proved"),
    ("rebuilt.ts", "missingIsNull", "refuted"),
    ("rebuilt.ts", "setsField", "refuted"),
    ("xf", "one_level", "proved"),
    ("xf", "two_levels", "open"),
]


@pytest.fixture(scope="module")
def reports():
    out = {}
    for name in sorted({n for n, _, _ in EXPECTED}):
        if name.endswith(".ts") and not HAS_NODE:
            continue
        root = CASES / name if (CASES / name).is_dir() else CASES
        out[name] = check([str(CASES / name)], CheckOptions(cache_path=None, lean=False), root=str(root))
    return out


@pytest.mark.parametrize("name,fn,status", EXPECTED)
def test_verdicts(reports, name, fn, status):
    if name not in reports:
        pytest.skip("frontend not available")
    got = {f.fn.name: f.status for f in reports[name].functions}
    assert got[fn] == status


def test_the_predicate_is_listed_as_an_assumption(reports):
    rep = reports["payload.py"]
    (f,) = [f for f in rep.functions if f.fn.name == "total_quantity"]
    assert any("trusted predicate 'valid_order'" in text for _, text in f.assumptions)


def test_an_aim_resting_on_a_predicate_says_so_everywhere(reports):
    rep = reports["payload.py"]
    (aim,) = [a for a in rep.aims if a.id == "ORDER-QTY"]
    assert aim.status == "partial" and aim.proved == 0 and aim.trusted == ["valid_item", "valid_order"]
    from telic.ledger import snapshot

    assert snapshot(rep)["functions"]["payload.py::total_quantity"]["status"] == "open"
    assert _aim_json(aim)["trusted"] == ["valid_item", "valid_order"]
    assert "assuming trusted valid_item, valid_order" in render_html(rep)


def test_typescript_lowering_is_proved():
    """telic's own reader of lower.mjs output: well-formed JSON in, no crash."""
    path = ROOT / "telic" / "frontend" / "typescript.py"
    rep = check([str(path)], CheckOptions(cache_path=None, lean=False, only=["_type", "_expr"]), root=str(ROOT))
    assert {f.fn.name: f.status for f in rep.functions if f.fn.name in ("_type", "_expr")} == {"_type": "proved", "_expr": "proved"}


def test_check_json_carries_the_assumption(tmp_path, capsys):
    from telic.cli import main

    main(["aims", str(CASES / "payload.py"), "--root", str(CASES), "--json", "--no-cache"])
    (aim,) = json.loads(capsys.readouterr().out)
    assert aim["trusted"] == ["valid_item", "valid_order"]


@pytest.mark.parametrize("name,fn,call", [("rebuilt.py", "present_is_not_null", "present_is_not_null({'k': None})"), ("rebuilt.ts", "missingIsNull", "missingIsNull({})")])
def test_a_refutation_shows_the_json_it_ran(reports, name, fn, call):
    if name not in reports:
        pytest.skip("frontend not available")
    (f,) = [f for f in reports[name].functions if f.fn.name == fn]
    (v,) = [v for v in f.verdicts if v.status == "refuted"]
    assert v.replay.confirmed and call_text(f.fn, v.model, f.ref.module.language) == call
