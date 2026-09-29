"""No exploit may be proved.

Every function in tests/cases/soundness/ that is not listed below carries a
contract that is false for the real program (see the README there); telic
must refute it, report it open, or reject the construct. Helpers whose
contracts are true are allowed to prove.
"""

from pathlib import Path

import pytest

from telic.checker import CheckOptions, check

from conftest import needs_node

DIR = Path(__file__).parent / "cases" / "soundness"

TRUE_HELPERS = {
    "t10.py": {"inc2", "sneaky"},
    "t11.py": {"inc2"},
    "t15.py": {"user"},
    "t18.py": {"inc2"},
    "t17.py": {"P.__post_init__"},
    "t19.py": {"Box.__init__", "weird", "decorated"},
    "t20.ts": {"Box.__init__"},
    "t22.py": {"Bag.__init__", "moved_ok"},
    "t23.rs": {"Counter.bump", "set_through"},
    "t21.py": {"B.__init__", "B.value", "C.value", "B.shrink", "other_task"},
    "t2.py": {"bump", "grow", "abs", "two"},
    "t6.py": {"inc"},
    "t7.py": {"setz", "first", "arith", "chained"},
    "t9.py": {"seqsum"},
    "t18.ts": {"inc"},
    "t3.ts": {"zero"},
    "t3_45.ts": {"zero"},
    "t3_5.ts": {"zero"},
    "t4.ts": {"zero"},
    "t5.ts": {"zeroLast"},
    "t8.ts": {"setz", "first", "mathRound"},
    "c2.ts": {"down", "other"},
    "crash1.py": {"copy"},
    "t24.py": {"is_neg", "fine", "Counter.__init__"},
    "t25.ts": {"fine"},
    "t26.rs": {"fine"},
    "t27.py": {"Box.__init__", "Box.get"},
}

FILES = sorted(p.name for p in DIR.iterdir() if p.suffix in (".py", ".ts", ".rs"))


@pytest.mark.parametrize("name", FILES)
def test_no_exploit_is_proved(name):
    if name.endswith(".ts"):
        import shutil

        if shutil.which("node") is None:
            pytest.skip("Node.js not available")
    if name.endswith(".rs"):
        pytest.importorskip("tree_sitter_rust")
    rep = check([str(DIR / name)], CheckOptions(cache_path=None, lean=False, timeout_ms=4000), root=str(DIR))
    proved = {f.fn.name for f in rep.functions if f.status == "proved"}
    unexpected = proved - TRUE_HELPERS.get(name, set())
    assert not unexpected, f"{name}: exploits proved: {sorted(unexpected)}"


@needs_node
def test_mirror_compares_exceptions():
    rep = check([str(DIR / "mir" / "g.ts")], CheckOptions(cache_path=None, lean=False), root=str(DIR))
    assert rep.mirrors and all(m.status != "proved" for m in rep.mirrors)


VACUOUS = [
    ("t24.py", "contradictory"),
    ("t24.py", "through_helper"),
    ("t24.py", "empty_below_zero"),
    ("t24.py", "split_across"),
    ("t24.py", "Impossible.get"),
    ("t24.py", "Counter.below_zero"),
    ("t25.ts", "contradictory"),
    ("t26.rs", "contradictory"),
]


@pytest.fixture(scope="module")
def vacuity_reports():
    out = {}
    for name in sorted({n for n, _ in VACUOUS}):
        if name.endswith(".ts"):
            import shutil

            if shutil.which("node") is None:
                continue
        if name.endswith(".rs"):
            try:
                import tree_sitter_rust  # noqa: F401
            except ImportError:
                continue
        out[name] = check([str(DIR / name)], CheckOptions(cache_path=None, lean=False, timeout_ms=4000), root=str(DIR))
    return out


@pytest.mark.parametrize("name,fn", VACUOUS)
def test_unsatisfiable_entry_is_vacuous(vacuity_reports, name, fn):
    if name not in vacuity_reports:
        pytest.skip("frontend not available")
    status = {f.fn.name: f.status for f in vacuity_reports[name].functions}
    assert status[fn] == "vacuous"


def test_intent_backed_only_by_a_vacuous_lemma_is_not_backed(vacuity_reports):
    (never,) = [i for i in vacuity_reports["t24.py"].intents if i.id == "NEVER"]
    assert never.status == "vacuous"


def test_vacuity_verdict_survives_the_cache(tmp_path):
    opts = CheckOptions(cache_path=str(tmp_path / "cache.json"), lean=False, timeout_ms=4000)
    for _ in range(2):
        rep = check([str(DIR / "t24.py")], opts, root=str(DIR))
        status = {f.fn.name: f.status for f in rep.functions}
        assert status["contradictory"] == "vacuous" and status["fine"] == "proved"
