"""Counterexamples whose inputs hold objects in maps, arrays and sets: the
solver's own model is decoded with the objects' fields and run."""

from pathlib import Path

import pytest

from telic.checker import CheckOptions, check
from telic.replay import call_text

from conftest import needs_node

CASES = Path(__file__).parent / "cases" / "containers"


@pytest.fixture(scope="module")
def report():
    return check([str(CASES / "locks.ts")], CheckOptions(cache_path=None, lean=False), root=str(CASES))


@needs_node
@pytest.mark.parametrize("fn,call", [("freeAt", "freeAt(locks: {0: <Lock #0 held=true>}, k: 0)"), ("firstFree", "firstFree([<Lock #0 held=true>])")])
def test_the_model_itself_replays_with_its_objects(report, fn, call):
    (f,) = [f for f in report.functions if f.fn.name == fn]
    (v,) = [v for v in f.verdicts if v.status == "refuted"]
    assert v.replay.confirmed and not getattr(v.replay, "fuzz_witness", None)
    assert call_text(f.fn, v.model, "typescript") == call


@needs_node
def test_a_set_is_not_made_up_as_json(report):
    (f,) = [f for f in report.functions if f.fn.name == "count"]
    assert f.status == "open" and call_text(f.fn, f.verdicts[0].model, "typescript") == "count(…)"
