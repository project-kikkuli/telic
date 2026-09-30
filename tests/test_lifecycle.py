"""Lifecycles: the grammar, the class-level checks, coverage, and aims."""

import json
from pathlib import Path

import pytest

from telic.checker import CheckOptions, check
from telic.cli import report_json
from telic.lifecycle import LifecycleError, closure, parse, texts

CASES = Path(__file__).parent / "cases" / "lifecycle"
EXAMPLES = Path(__file__).parent.parent / "examples"


@pytest.mark.parametrize(
    "payload, kind, field, edges, expr",
    [
        ("status: A -> B -> C", "graph", "status", [("A", "B"), ("B", "C")], ""),
        ("self.status: A | B -> C, C -> A", "graph", "status", [("A", "C"), ("B", "C"), ("C", "A")], ""),
        ("this.s: Status::Open -> Status::Won", "graph", "s", [("Status::Open", "Status::Won")], ""),
        ('stage: "draft" -> "live"', "graph", "stage", [('"draft"', '"live"')], ""),
        ("never status: SHIPPED -> PENDING", "never", "status", [("SHIPPED", "PENDING")], ""),
        ("monotonic self.paid", "monotonic", "", [], "self.paid"),
        ("once self.status == Status.WON", "once", "", [], "self.status == Status.WON"),
        ("implies(old(self.closed), self.closed)", "step", "", [], "implies(old(self.closed), self.closed)"),
        ("this.v <= old(this.v) || this.v == 0", "step", "", [], "this.v <= old(this.v) || this.v == 0"),
    ],
)
def test_parse(payload, kind, field, edges, expr):
    f = parse(payload)
    assert (f.kind, f.field, f.edges, f.expr) == (kind, field, edges, expr)


@pytest.mark.parametrize("payload", ["", "status: A", "status: A ->", "never status", "monotonic", "self.x > 0"])
def test_parse_rejects(payload):
    with pytest.raises(LifecycleError):
        parse(payload)


@pytest.mark.parametrize(
    "edges, pairs",
    [
        ([("A", "B"), ("B", "C")], {("A", "B"), ("A", "C"), ("B", "C")}),
        ([("A", "B"), ("B", "A")], {("A", "B"), ("B", "A")}),
        ([("A", "B"), ("C", "D")], {("A", "B"), ("C", "D")}),
    ],
)
def test_closure_is_every_path(edges, pairs):
    assert set(closure(edges)) == pairs


@pytest.mark.parametrize("lang, eq, conj", [("python", "==", " and "), ("typescript", "===", " && "), ("rust", "==", " && ")])
def test_relation_is_host_syntax(lang, eq, conj):
    t = texts(parse("s: A -> B"), lang)
    this = "this" if lang == "typescript" else "self"
    assert t.relation == f"old({this}.s) {eq} {this}.s {'||' if lang != 'python' else 'or'} (old({this}.s) {eq} A{conj}{this}.s {eq} B)"
    assert [label for label, _, _ in t.probes] == ["A -> B"]


def run(path: Path):
    return check([str(path)], CheckOptions(cache_path=None, lean=False), root=str(path.parent))


def test_subscription_example_is_backed():
    rep = run(EXAMPLES / "subscription.py")
    assert rep.ok
    assert {lc.clause.text: lc.status for lc in rep.lifecycles} == {lc.clause.text: "proved" for lc in rep.lifecycles}
    assert all(not s.unknown and s.by for lc in rep.lifecycles for s in lc.steps)
    assert {a.id: a.status for a in rep.aims} == {"CANCEL-FINAL": "backed", "CHARGES-KEPT": "backed"}
    assert all(not a.pointers for a in rep.aims)


def test_coverage_and_vacuity():
    rep = run(CASES / "coverage.py")
    by = {lc.clause.text: lc for lc in rep.lifecycles}
    graph = by["mode: 0 -> 1 -> 2, 1 -> 0"]
    assert graph.status == "proved"
    assert {s.label: s.by for s in graph.steps} == {"0 -> 1": ["Vault.arm"], "1 -> 2": ["Vault.fire"], "1 -> 0": []}
    # nothing seals a vault: 'once sealed' holds only because it never becomes true
    once = by["once self.sealed"]
    assert once.status == "vacuous"
    assert "never true" in once.problems[0]
    assert by["never mode: 2 -> 0"].status == "proved"
    (aim,) = rep.aims
    assert aim.status == "vacuous"


def test_misplaced_and_malformed_lines_are_reported():
    rep = run(CASES / "misplaced.py")
    msgs = [msg for m in rep.modules for msg, _ in m.problems]
    assert any("stray '@lifecycle'" in m for m in msgs)
    assert any("write 'FIELD: A -> B'" in m for m in msgs)
    assert any("only read fields of the object itself" in m for m in msgs)


def test_json_lists_lifecycles():
    rep = run(CASES / "coverage.py")
    out = json.loads(json.dumps(report_json(rep)))
    rows = {x["text"]: x for x in out["lifecycles"]}
    assert rows["once self.sealed"]["status"] == "vacuous"
    assert rows["mode: 0 -> 1 -> 2, 1 -> 0"]["steps"][2] == {"step": "1 -> 0", "by": [], "unknown": False}


def test_unchecked_code_changes_objects_only_in_its_own_language():
    rep = check([str(CASES / "crosslang")], CheckOptions(cache_path=None, lean=False, replay=False), root=str(CASES / "crosslang"))
    got = {lc.module.language: lc.status for lc in rep.lifecycles}
    assert got == {"python": "proved", "typescript": "open"}
