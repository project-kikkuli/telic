"""No exploit may be proved.

Every function in tests/cases/soundness/ that is not listed below carries a
contract that is false for the real program (see the README there); telic
must refute it, report it open, or reject the construct. Helpers whose
contracts are true are allowed to prove. A proof that rests on a contract
telic could not prove (a callee, or an override a call may dispatch to) is
not a proof: it names the unproved contract.
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
    "t30.ts": {"Shape.area", "Shape.__init__", "Square.__init__"},
    "t31.py": {"claim", "claim2"},  # proved only assuming the recursion, which stays open
    "inh1.py": {"Base.__init__", "Base.setx", "Base.helper", "Sub.__init__"},
    "inh2.py": {"Base.size", "Sub.size"},
    "async1.py": {"Counter.__init__", "bump"},
    "async1.ts": {"Counter.__init__", "bump", "set"},
    "inh1.ts": {"Base.__init__", "Base.setx", "Base.helper"},
    "inh2.ts": {"Base.size", "Sub.size"},
    "inh3.ts": {"A.__init__"},
    "inh4.ts": {"A.__init__", "A.m", "A.viaSuper", "B.__init__", "B.m"},
    "inh5.ts": {"A.__init__", "A.f"},
    "alias1.ts": {"flip", "grow", "Holder.__init__"},
    "alias2.ts": {"setKind", "nested", "orElse", "pick", "same", "push", "via"},
    "t32.py": {"Acct.__init__", "refill", "clamp", "refill_nested"},
    "t32.ts": {"Acct.__init__", "refill"},
    "t33.py": {"Acct.__init__", "sees"},
    "t33.ts": {"Acct.__init__", "sees"},
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
    proved = {f.fn.name for f in rep.functions if f.status == "proved" and not f.open_deps}
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


def test_aim_backed_only_by_a_vacuous_lemma_is_not_backed(vacuity_reports):
    (never,) = [i for i in vacuity_reports["t24.py"].aims if i.id == "NEVER"]
    assert never.status == "vacuous"


def test_vacuity_verdict_survives_the_cache(tmp_path):
    opts = CheckOptions(cache_path=str(tmp_path / "cache.json"), lean=False, timeout_ms=4000)
    for _ in range(2):
        rep = check([str(DIR / "t24.py")], opts, root=str(DIR))
        status = {f.fn.name: f.status for f in rep.functions}
        assert status["contradictory"] == "vacuous" and status["fine"] == "proved"


def test_mirror_with_disjoint_preconditions_is_vacuous():
    rep = check([str(DIR / "mirvac")], CheckOptions(cache_path=None, lean=False), root=str(DIR / "mirvac"))
    assert [m.status for m in rep.mirrors] == ["vacuous"]
    assert [i.status for i in rep.aims if i.id == "SAME"] == ["vacuous"]


DIVERGES = """
def down(n: int) -> int:
    #@ decreases n
    if n <= 0:
        return 0
    return down(n + 1) + 1


def uses_down(x: int) -> int:
    #@ ensures result == 42 or down(3) == 0
    return x
"""


@pytest.mark.parametrize("engine", ["python", "ox"])
def test_the_timeout_bounds_unfolding_a_diverging_definition(tmp_path, engine):
    from telic.engine import binary

    if engine == "ox" and binary() is None:
        pytest.skip("telic-core not built")
    (tmp_path / "m.py").write_text(DIVERGES)
    opts = CheckOptions(cache_path=None, lean=False, replay=False, timeout_ms=1000, engine=engine, only={"uses_down"})
    rep = check([str(tmp_path / "m.py")], opts, root=str(tmp_path))
    (f,) = rep.functions
    assert f.status == "open" and [v.reason for v in f.verdicts] == ["timeout"]


def test_non_terminating_recursion_backs_no_aim():
    rep = check([str(DIR / "t31.py")], CheckOptions(cache_path=None, lean=False, timeout_ms=4000), root=str(DIR))
    status = {f.fn.name: f.status for f in rep.functions}
    assert status["spin"] != "proved" and status["ping"] != "proved"
    assert [i.status for i in rep.aims] == ["partial"]
