"""The native engine (core/) agrees with the Python core, obligation by obligation.

Skipped when ``telic-core`` has not been built (``make -C core`` with OxCaml).
"""

import json
from pathlib import Path

import pytest

from telic import engine
from telic.checker import CheckOptions, ProofCache, _math_schema, build_theory, check, load_modules, obligation_key, solve_all
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
    cache_path = Path(__file__).resolve().parent.parent / ".telic" / "cache.json"
    cache = ProofCache(str(cache_path))
    from telic.toolchain import native_z3

    res = engine.run(p, th, tasks, 60000, RLIMIT, None, [k[3:] for k, v in cache.data.items() if k.startswith("ox:") and v.get("method") == "z3"], json.dumps(native_z3(), sort_keys=True))
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
    pending = []
    py_status = {}
    for ref, _, obs in generated:
        for ob in obs:
            key = obligation_key(ob, th, RLIMIT, 60000, _math_schema(p, ref))
            hit = cache.get(key)
            if hit is not None and hit.get("method") == "z3":
                py_status[key] = "proved"
            else:
                pending.append((key, ob))
    for (key, ob), result in zip(pending, solve_all([ob for _, ob in pending], th, 60000, RLIMIT, None)):
        py_status[key] = result.status
        if result.status == "proved":
            cache.put(key, {"method": "z3"})
    for ref, r, obs in generated:
        py = {o.id: py_status[obligation_key(o, th, RLIMIT, 60000, _math_schema(p, ref))] for o in obs}
        ox = {o["ob"].id: o["status"] for o in r["obligations"]}
        if set(py) != set(ox):
            diffs.append(f"{ref.key}: obligations differ {sorted(set(py) ^ set(ox))}")
        for k in py.keys() & ox.keys():
            compared += 1
            # "unknown" may differ by timing; a proved/refuted split may not.
            if py[k] != ox[k] and "unknown" not in (py[k], ox[k]):
                diffs.append(f"{k}: python {py[k]}, engine {ox[k]}")
        for o in r["obligations"]:
            if o["status"] == "proved":
                cache.put("ox:" + o["key"], {"method": "z3"})
    cache.save()
    return compared, diffs


DIFF_CASES = ["corpus.py", "corpus.ts", "corpus.rs", "corpus.swift"] + sorted(f"objects/{p.name}" for p in (CASES / "objects").iterdir() if p.suffix in (".py", ".ts"))


@pytest.mark.parametrize("name", DIFF_CASES)
def test_engine_agrees_with_python_core(name):
    if name.endswith(".ts") and not HAS_NODE:
        pytest.skip("Node.js not available")
    if name.endswith(".rs"):
        pytest.importorskip("tree_sitter_rust")
    if name.endswith(".swift"):
        pytest.importorskip("tree_sitter_swift")
    compared, diffs = _differential(CASES / name)
    assert compared > 20
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
def test_engine_reuses_the_obligation_cache(monkeypatch, name):
    monkeypatch.setenv("TELIC_ENGINE", "ox")
    path = CASES / name
    cache = Path(__file__).resolve().parent.parent / ".telic" / "cache.json"
    opts = CheckOptions(cache_path=str(cache), lean=False, replay=False, receipts=False, engine="ox")
    first = check([str(path)], opts, root=str(path.parent))
    second = check([str(path)], opts, root=str(path.parent))
    proved = lambda rep: {v.ob.id for f in rep.functions for v in f.verdicts if v.status == "proved"}  # noqa: E731
    assert proved(first) and proved(first) == proved(second)
    assert second.cache_hits >= len(proved(first))


def test_native_query_receipt_ignores_unrelated_term_id_shifts(tmp_path):
    from telic.toolchain import native_z3

    salt = json.dumps(native_z3(), sort_keys=True)
    target = "def target(x: int) -> int:\n    #@ requires x >= 0\n    #@ ensures result >= x\n    return x + 1\n"
    unrelated = "def unrelated(x: int) -> int:\n    #@ ensures result == x * 23 + 17\n    return (x + 1) * 23 - 6\n\n"

    def run(source, cached=()):
        path = tmp_path / "m.py"
        path.write_text(source)
        modules = load_modules([str(path)], str(tmp_path))
        program = Program.build(modules)
        theory, _ = build_theory(program, {})
        ref = next(ref for ref in program.funcs.values() if ref.fn.name == "target")
        result = engine.run(program, theory, [(ref, Options())], 60000, RLIMIT, None, list(cached), salt)
        return result[ref.key]["obligations"]

    first = run(target)
    keys = [ob["key"] for ob in first if ob["status"] == "proved"]
    assert keys
    shifted = run(unrelated + target, keys)
    assert shifted and all(ob["status"] == "proved" and ob["reason"] == "cache" for ob in shifted)


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


def test_a_replaced_binary_is_revalidated_at_the_same_path(tmp_path, monkeypatch):
    exe = tmp_path / "telic-core"
    monkeypatch.setenv("TELIC_CORE", str(exe))
    monkeypatch.setattr(engine, "_FRESH", set())
    monkeypatch.setattr(engine, "source_hash", lambda: "current-sources")
    exe.write_text("#!/bin/sh\nprintf 'current-sources\\n'\n")
    exe.chmod(0o755)
    assert engine.binary() == str(exe)

    exe.write_text("#!/bin/sh\nprintf 'stale-sources\\n'\n")
    exe.chmod(0o755)
    with pytest.raises(RuntimeError, match="stale.*make -C"):
        engine.binary()
