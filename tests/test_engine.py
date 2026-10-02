"""The native engine (core/) agrees with the Python core, obligation by obligation.

Skipped when ``telic-core`` has not been built (``make -C core`` with OxCaml).
"""

from pathlib import Path

import pytest

from telic import engine
from telic.checker import CheckOptions, build_theory, check, load_modules, solve_all
from telic.program import Program
from telic.infer import infer_rlimit
from telic.smt import RLIMIT
from telic.vcgen import Options, VCError, VCGen

from conftest import HAS_NODE

CASES = Path(__file__).parent / "cases"

pytestmark = pytest.mark.skipif(engine.binary() is None, reason="telic-core not built")


def _differential(path: Path):
    mods = load_modules([str(path)], str(path.parent))
    p = Program.build(mods)
    th, _ = build_theory(p, {})
    tasks = [(r, Options()) for r in p.funcs.values() if not r.fn.unsupported and not r.fn.trusted and not r.module.context]
    res = engine.run(p, th, tasks, 60000, RLIMIT, None)
    assert res is not None
    diffs, compared, generated = [], 0, []
    for ref, _ in tasks:
        r = res[ref.key]
        if r["status"] != "ok":
            diffs.append(f"{ref.key}: engine fell back: {r.get('reason')}")
            continue
        try:
            generated.append((ref, r, VCGen(p, ref).run()))
        except VCError:
            diffs.append(f"{ref.key}: engine generated VCs the Python core rejects")
    solved = iter(solve_all([o for _, _, obs in generated for o in obs], th, 60000, RLIMIT, None))
    for ref, r, obs in generated:
        py = {o.id: next(solved).status for o in obs}
        ox = {o["ob"].id: o["status"] for o in r["obligations"]}
        if set(py) != set(ox):
            diffs.append(f"{ref.key}: obligations differ {sorted(set(py) ^ set(ox))}")
        for k in py.keys() & ox.keys():
            compared += 1
            # "unknown" may differ by timing; a proved/refuted split may not.
            if py[k] != ox[k] and "unknown" not in (py[k], ox[k]):
                diffs.append(f"{k}: python {py[k]}, engine {ox[k]}")
    return compared, diffs


DIFF_CASES = ["corpus.py", "corpus.ts", "corpus.rs", "corpus.swift", "soundness/t45.py", "soundness/t46.py", "soundness/t47.py", "soundness/t48.ts", "soundness/t49.py", "soundness/t50.py", "soundness/t51.py", "soundness/t53.py", "soundness/t54.py"] + sorted(f"objects/{p.name}" for p in (CASES / "objects").iterdir() if p.suffix in (".py", ".ts"))


@pytest.mark.parametrize("name", DIFF_CASES)
def test_engine_agrees_with_python_core(name):
    if name.endswith(".ts") and not HAS_NODE:
        pytest.skip("Node.js not available")
    if name.endswith(".rs"):
        pytest.importorskip("tree_sitter_rust")
    if name.endswith(".swift"):
        pytest.importorskip("tree_sitter_swift")
    compared, diffs = _differential(CASES / name)
    assert compared > (0 if name.startswith("soundness/") else 20)
    assert not diffs, "\n".join(diffs)


def test_engine_models_everything_in_the_corpora():
    """No fallbacks: every function the Python core checks, the engine checks."""
    for name in DIFF_CASES:
        if name.endswith(".ts") and not HAS_NODE:
            continue
        if name.endswith(".rs"):
            try:
                import tree_sitter_rust  # noqa: F401
            except ImportError:
                continue
        if name.endswith(".swift"):
            try:
                import tree_sitter_swift  # noqa: F401
            except ImportError:
                continue
        path = CASES / name
        p = Program.build(load_modules([str(path)], str(path.parent)))
        th, _ = build_theory(p, {})
        tasks = [(r, Options()) for r in p.funcs.values() if not r.fn.unsupported and not r.fn.trusted and not r.module.context]
        res = engine.run(p, th, tasks, 60000, RLIMIT, None) or {}
        fell = [f"{k}: {r.get('reason')}" for k, r in res.items() if r["status"] == "fallback"]
        assert not fell, f"{name}: {fell}"


def test_engine_proves_no_exploit():
    from test_soundness import DIR, FILES, TRUE_HELPERS

    bad = []
    for name in FILES:
        if name.endswith(".ts") and not HAS_NODE:
            continue
        if name.endswith(".swift"):
            try:
                import tree_sitter_swift  # noqa: F401
            except ImportError:
                continue
        rep = check([str(DIR / name)], CheckOptions(cache_path=None, lean=False, engine="ox"), root=str(DIR))
        proved = {f.fn.name for f in rep.functions if f.status == "proved" and not f.open_deps}
        bad += [f"{name}:{n}" for n in proved - TRUE_HELPERS.get(name, set())]
    assert not bad, f"exploits proved by the engine: {bad}"


@pytest.mark.parametrize("name", ["corpus.py", "corpus.ts"])
def test_engine_infers_what_python_infers(name):
    from telic.infer import infer

    if name.endswith(".ts") and not HAS_NODE:
        pytest.skip("Node.js not available")
    path = CASES / name
    p = Program.build(load_modules([str(path)], str(path.parent)))
    th, _ = build_theory(p, {})
    refs = [r for r in p.funcs.values() if not r.fn.unsupported and not r.fn.trusted and not r.module.context]
    ox = engine.infer(p, th, refs, 60000, infer_rlimit(RLIMIT), None)
    diffs = []
    for r in refs:
        mine = ox.get(r.key)
        if mine is None:
            diffs.append(f"{r.key}: engine fell back")
        elif mine.summary() != infer(p, r, th).summary():
            diffs.append(f"{r.key}: {mine.summary()} vs {infer(p, r, th).summary()}")
    assert not diffs, "\n".join(diffs)


@pytest.mark.parametrize("name", ["corpus.py", "objects/bank.py"])
def test_engine_reuses_the_obligation_cache(tmp_path, monkeypatch, name):
    monkeypatch.setenv("TELIC_ENGINE", "ox")
    path = CASES / name
    opts = CheckOptions(cache_path=str(tmp_path / "cache.json"), lean=False, replay=False, receipts=False, engine="ox")
    first = check([str(path)], opts, root=str(path.parent))
    second = check([str(path)], opts, root=str(path.parent))
    proved = lambda rep: {v.ob.id for f in rep.functions for v in f.verdicts if v.status == "proved"}  # noqa: E731
    assert proved(first) and proved(first) == proved(second)
    assert second.cache_hits >= len(proved(first))


def test_a_field_telic_cannot_model_fails_only_what_touches_it():
    path = CASES / "unmodelled.py"
    by = {}
    for eng in ("python", "ox"):
        rep = check([str(path)], CheckOptions(cache_path=None, lean=False, replay=False, engine=eng), root=str(path.parent))
        by[eng] = {f.fn.name: f.status for f in rep.functions}
    assert by["python"] == by["ox"]
    assert by["ox"]["Log.bump"] == "proved" and by["ox"]["Log.__init__"] == "error"


def test_a_binary_built_from_other_sources_is_refused(monkeypatch):
    monkeypatch.setattr(engine, "_FRESH", set())
    monkeypatch.setattr(engine, "source_hash", lambda: "not-these-sources")
    with pytest.raises(RuntimeError, match="stale.*make -C"):
        engine.binary()


@pytest.mark.parametrize("engine_name", ["python", "ox"])
def test_engine_rounds_wide_float_literals_from_exact_rationals(tmp_path, engine_name):
    literal = "1.000000000000000300000000000000000000000000000000000000000000000000001"
    path = tmp_path / "wide_literal.ts"
    path.write_text(
        "export function f(): number {\n"
        "  //@ ensures result == 1.0000000000000002\n"
        f"  return {literal};\n"
        "}\n"
    )
    rep = check([str(path)], CheckOptions(cache_path=None, lean=False, replay=False, engine=engine_name), root=str(tmp_path))
    assert {f.status for f in rep.functions} == {"proved"}
