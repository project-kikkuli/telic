"""No exploit may be proved.

Every function in tests/cases/soundness/ that is not listed below carries a
contract that is false for the real program (see the README there); telic
must refute it, report it open, or reject the construct. Helpers whose
contracts are true are allowed to prove. A proof that rests on a contract
telic could not prove (a callee, or an override a call may dispatch to) is
not a proof: it names the unproved contract.
"""

import json
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

from telic.checker import CheckOptions, check

from conftest import run_check, needs_node

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
    "t37.py": {"Loop.__post_init__"},
    "t38.py": {"knot"},
    "t39.py": {"knot"},
    "t40.py": {"knot"},
    "t41.py": {"knot", "Loop.nxt"},
    "t42.py": {"wraps_deco", "plain_deco"},
    "t42.ts": {"wrap"},
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
    "swift1.swift": {"Box.init", "mayThrow", "runIt", "Ten.size", "Three.size", "Five.value", "Six.value"},
    "swift2.swift": {"One.value", "Base.init", "Base.v", "ViaAlias.v", "throughAlias", "check", "Span.init"},  # throughAlias: proved only assuming Negative.value, which is refuted
    "t34.py": {"nonneg", "dip", "Acct.__init__", "Link.__init__", "Pool.__init__"},
    "t34.ts": {"nonneg", "dip", "Acct.__init__", "Link.__init__", "Pool.__init__"},
    "t35.py": {"Acct.__init__", "Checked.__init__"},
    "t35.ts": {"Acct.__init__", "Checked.__init__"},
    "t36.py": {"Acct.__init__", "peek", "Base.__init__", "Capped.__init__", "lift", "first_v"},
    "t36.ts": {"Acct.__init__", "peek", "Base.__init__", "Capped.__init__", "lift"},
    "lc1.py": {"Counter.__init__", "Counter.bump", "Job.__init__", "Job.start", "Job.finish", "Base.__init__", "Door.__init__", "Door.lock", "Valve.__init__"},
    "lc1.ts": {"Meter.__init__", "Meter.tick", "Lock.__init__", "Lock.seal", "Stepper.__init__", "Stepper.next"},
    "lc2.py": {"Tab.__init__", "Tab.pay", "Gauge.__init__", "Latch.__init__", "Latch.close", "Meter.__init__", "Meter.tick"},
    "lc2.rs": {"Tally.bump"},
    "json_mutate.py": {"put"},
    "json_mutate.rs": {"clear"},
    "t31.rs": {"f", "f@two", "Ctr.reset", "E2.from", "Five.w", "Loose.eq", "Tr.w@default", "fails", "wrap"},
    "t32.rs": {"set"},
    "t43.py": {"pos", "grow", "Counter.__init__", "Counter.bump"},
    "t43.ts": {"pos", "Counter.__init__", "Counter.bump"},
    "float1.py": {"fine"},
    "float1.ts": {"fine"},
    "float1.rs": {"fine", "to_int"},
    "float1.swift": {"fine"},
}

# Lifecycles whose claim across calls is true; every other one in these files is false.
TRUE_LIFECYCLES = {
    "lc1.py": {"state: 0 -> 1 -> 2"},
    "lc1.ts": {"stage: 0 -> 1 -> 2"},
}

FILES = sorted(p.name for p in DIR.iterdir() if p.suffix in (".py", ".ts", ".rs", ".swift"))


@pytest.mark.parametrize("name", FILES)
def test_no_exploit_is_proved(name):
    if name.endswith(".ts"):
        import shutil

        if shutil.which("node") is None:
            pytest.skip("Node.js not available")
    if name.endswith(".rs"):
        pytest.importorskip("tree_sitter_rust")
    if name.endswith(".swift"):
        pytest.importorskip("tree_sitter_swift")
    rep = check([str(DIR / name)], CheckOptions(cache_path=None, lean=False), root=str(DIR))
    proved = {f.fn.name for f in rep.functions if f.status == "proved" and not f.open_deps}
    unexpected = proved - TRUE_HELPERS.get(name, set())
    assert not unexpected, f"{name}: exploits proved: {sorted(unexpected)}"
    lifecycles = {lc.clause.text for lc in rep.lifecycles if lc.status == "proved"} - TRUE_LIFECYCLES.get(name, set())
    assert not lifecycles, f"{name}: false lifecycles proved: {sorted(lifecycles)}"


def test_mirror_sides_keep_their_own_symbols():
    rep = check([str(DIR / "mircomp")], CheckOptions(cache_path=None, lean=False), root=str(DIR / "mircomp"))
    got = {m.b.fn.name: m for m in rep.mirrors}
    assert set(got) == {"g", "h"}
    assert all(m.status == "refuted" and m.witness["replay"]["confirmed"] for m in got.values())


@needs_node
def test_strings_are_not_compared_symbolically_across_languages():
    rep = check([str(DIR / "mirstr")], CheckOptions(cache_path=None, lean=False), root=str(DIR / "mirstr"))
    got = {m.b.fn.name: m for m in rep.mirrors}
    assert set(got) == {"size", "before"}
    assert all(m.status == "refuted" and m.witness["replay"]["confirmed"] for m in got.values())


# Float claims a rational model proves; each is refuted by a run of the real program.
FLOAT_REFUTED = [
    ("float1.py", ["classic", "reflexive", "zero_sign", "grows", "neg_zero", "exact_compare", "big_int", "held"]),
    ("float1.ts", ["classic", "reflexive", "inc", "unsafe", "backAndForth", "floorUp", "tax"]),
    ("float1.rs", ["classic", "reflexive", "grows", "nan_cast", "neg_zero"]),
    ("float1.swift", ["classic", "reflexive", "grows", "zeroSign"]),
]


@pytest.mark.parametrize("name,fns", FLOAT_REFUTED)
def test_false_float_claims_are_refuted_by_the_runtime(name, fns):
    if name.endswith(".ts"):
        if shutil.which("node") is None:
            pytest.skip("Node.js not available")
    if name.endswith(".rs"):
        pytest.importorskip("tree_sitter_rust")
        if shutil.which("cargo") is None and shutil.which("rustc") is None:
            pytest.skip("rustc not available")
    if name.endswith(".swift"):
        pytest.importorskip("tree_sitter_swift")
        if shutil.which("swiftc") is None:
            pytest.skip("swiftc not available")
    rep = check([str(DIR / name)], CheckOptions(cache_path=None, lean=False), root=str(DIR))
    status = {f.fn.name: f.status for f in rep.functions}
    wrong = {fn: status.get(fn) for fn in fns if status.get(fn) != "refuted"}
    assert not wrong, f"{name}: not refuted by a replayed counterexample: {wrong}"


@needs_node
def test_float_mirrors_differ_across_summation_orders():
    rep = check([str(DIR / "mirfloat")], CheckOptions(cache_path=None, lean=False), root=str(DIR / "mirfloat"))
    got = {m.b.fn.name: m for m in rep.mirrors}
    assert set(got) == {"total", "add3"}
    assert all(m.status != "proved" for m in got.values())
    assert got["add3"].status == "refuted" and got["add3"].witness["replay"]["confirmed"]


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
    ("json_liar.py", "liar"),
    ("json_liar.py", "use_liar"),
    ("json_liar.py", "p"),
    ("json_liar.py", "q"),
    ("json_deep_liar.py", "sums"),
    ("json_deep_liar.py", "sums_from"),
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
        out[name] = check([str(DIR / name)], CheckOptions(cache_path=None, lean=False), root=str(DIR))
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
    opts = CheckOptions(cache_path=str(tmp_path / "cache.json"), lean=False)
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
    rep = check([str(DIR / "t31.py")], CheckOptions(cache_path=None, lean=False), root=str(DIR))
    status = {f.fn.name: f.status for f in rep.functions}
    assert status["spin"] != "proved" and status["ping"] != "proved"
    assert [i.status for i in rep.aims] == ["partial"]


HIDDEN = {
    "t42.py": ("claim_rebound", "claim_lambda", "claim_wraps", "claim_decorated", "claim_aliased", "claim_passed", "claim_constructor"),
    "t42.ts": ("claimRebound", "claimWrapped", "claimCall", "claimBind", "claimPassed"),
}


def _raises(name: str, fn: str) -> str:
    if name.endswith(".py"):
        code = f"import {name[:-3]} as m\ntry:\n    m.{fn}(0)\nexcept RecursionError:\n    print('RecursionError')"
        return subprocess.run([sys.executable, "-c", code], capture_output=True, text=True, cwd=DIR).stdout.strip()
    ts_path = Path(__file__).parent.parent / "telic" / "frontend" / "ts" / "node_modules" / "typescript"
    js = (
        f"const ts = require({json.dumps(str(ts_path))});\n"
        f"const src = require('fs').readFileSync({json.dumps(str(DIR / name))}, 'utf8');\n"
        "const out = ts.transpileModule(src, { compilerOptions: { module: ts.ModuleKind.CommonJS, target: ts.ScriptTarget.ES2022 } }).outputText;\n"
        "const m = { exports: {} }; new Function('module', 'exports', out)(m, m.exports);\n"
        f"try {{ m.exports[{json.dumps(fn)}](0); }} catch (e) {{ console.log(e.constructor.name); }}\n"
    )
    return subprocess.run(["node", "-e", js], capture_output=True, text=True).stdout.strip()


@pytest.mark.parametrize("name,fn", [(n, f) for n, fs in HIDDEN.items() for f in fs])
def test_recursion_through_a_function_value_really_recurses(name, fn):
    if name.endswith(".ts") and shutil.which("node") is None:
        pytest.skip("Node.js not available")
    assert _raises(name, fn) == ("RecursionError" if name.endswith(".py") else "RangeError")


SCHEDULED = """function link(label: string): HTMLElement {
  const a = document.createElement('a')
  a.textContent = label
  a.addEventListener('click', () => render())
  setTimeout(() => render(), 10)
  return a
}

function render(): void {
  document.body.replaceChildren(link('home'))
}

function spin(n: number): number {
  return [n].map((x) => spin(x))[0]
}
"""


@needs_node
def test_a_scheduled_callback_is_not_recursion(tmp_path):
    rep = run_check(tmp_path, {"m.ts": SCHEDULED}, lean=False)
    open_ = {f.fn.name for f in rep.functions if f.status != "proved" and (f.problems or f.verdicts)}
    assert open_ == {"spin"}
