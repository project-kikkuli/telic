"""The Rust frontend: verdicts pinned in tests/cases/corpus.rs, and
refutations confirmed by running the code compiled with rustc."""

import re
import shutil
import subprocess
from pathlib import Path

import pytest

pytest.importorskip("tree_sitter_rust")

from telic.checker import CheckOptions, check  # noqa: E402

CORPUS = Path(__file__).parent / "cases" / "corpus.rs"
HAS_RUSTC = shutil.which("rustc") is not None


def expectations(path: Path) -> dict[str, str]:
    """``// expect: <verdict>`` above a function, keyed as telic names it:
    ``f``, ``Type.m`` in an impl, ``Trait.m@default`` for a trait's default body."""
    out, owner, depth, trait = {}, None, 0, False
    pending = None
    for line in path.read_text().splitlines():
        m = re.match(r"\s*(?:pub\s+)?(impl|trait)\b(?:<[^>]*>)?\s+(?:[\w:]+(?:<[^>]*>)?\s+for\s+)?(\w+)[^{]*\{", line)
        if m:
            owner, depth, trait = m.group(2), 0, m.group(1) == "trait"
        if owner is not None:
            depth += line.count("{") - line.count("}")
            if depth <= 0 and "}" in line and not m:
                owner = None
        e = re.match(r"\s*// expect: (\w+)", line)
        if e:
            pending = e.group(1)
            continue
        d = re.match(r"\s*(?:pub\s+)?fn\s+(\w+)", line)
        if d and pending:
            name = f"{owner}.{d.group(1)}" if owner else d.group(1)
            out[name + ("@default" if trait and line.rstrip().endswith("{") else "")] = pending
            pending = None
    return out


@pytest.fixture(scope="module")
def report():
    rep = check([str(CORPUS)], CheckOptions(cache_path=None, lean=False), root=str(CORPUS.parent))
    return rep, {f.fn.name: f for f in rep.functions}


@pytest.mark.skipif(not HAS_RUSTC, reason="rustc not available")
def test_corpus_is_valid_rust(tmp_path):
    p = subprocess.run(["rustc", "--edition", "2021", "--crate-type", "lib", str(CORPUS), "-o", str(tmp_path / "c.rlib")], capture_output=True, text=True)
    assert p.returncode == 0, p.stderr


def test_rust_corpus(report):
    rep, got = report
    assert not [p for m in rep.modules for p in m.problems]
    bad = []
    for name, want in expectations(CORPUS).items():
        f = got.get(name)
        have = f.status if f else "missing"
        if have != want:
            detail = [f"{v.ob.id}:{v.status}" for v in f.verdicts if v.status != "proved"] if f else []
            bad.append(f"{name}: expected {want}, got {have} {detail} {f.problems if f else ''}")
    assert not bad, "\n".join(bad)


@pytest.mark.skipif(not HAS_RUSTC, reason="rustc not available")
def test_rust_refutations_are_real_panics(report):
    _, got = report
    for name, want in expectations(CORPUS).items():
        if want != "refuted":
            continue
        vs = [v for v in got[name].verdicts if v.status == "refuted"]
        confirmed = [v for v in vs if v.replay is not None and v.replay.confirmed]
        assert confirmed, (name, [(v.ob.id, v.replay.summary if v.replay else None) for v in vs])


CRATE = Path(__file__).parent / "cases" / "rust_crate"


@pytest.fixture(scope="module")
def crate_report():
    rep = check([str(CRATE)], CheckOptions(cache_path=None, lean=False), root=str(CRATE))
    return rep, {(f.ref.module.path, f.fn.name): f for f in rep.functions}


def test_crate_across_files(crate_report):
    rep, got = crate_report
    assert not [p for m in rep.modules for p in m.problems]
    bad = []
    for src in sorted((CRATE / "src").rglob("*.rs")):
        rel = str(src.relative_to(CRATE))
        for name, want in expectations(src).items():
            f = got.get((rel, name))
            have = f.status if f else "missing"
            if have != want:
                bad.append(f"{rel}::{name}: expected {want}, got {have}")
    assert not bad, "\n".join(bad)


def test_crate_file_alone_uses_its_crate():
    """Checking one file of a crate still resolves what other files declare."""
    rep = check([str(CRATE / "src" / "lib.rs")], CheckOptions(cache_path=None, lean=False), root=str(CRATE))
    assert {f.fn.name: f.status for f in rep.functions} == {"big": "proved", "clamped": "proved", "both": "proved"}


@pytest.mark.skipif(not HAS_RUSTC, reason="rustc not available")
def test_crate_is_valid_rust_and_refutations_replay(crate_report, tmp_path):
    p = subprocess.run(["rustc", "--edition", "2021", "--crate-type", "lib", str(CRATE / "src" / "lib.rs"), "-o", str(tmp_path / "c.rlib")], capture_output=True, text=True)
    assert p.returncode == 0, p.stderr
    _, got = crate_report
    refuted = [f for f in got.values() if f.status == "refuted"]
    assert refuted
    for f in refuted:
        assert any(v.replay is not None and v.replay.confirmed for v in f.verdicts if v.status == "refuted"), f.fn.name


def _sample(ty, kind, rng, fe, depth=0):
    """A value of a checked type, in the shape counterexample models have."""
    from telic import ir
    from telic.frontend.rust import INT_KINDS, int_range

    if isinstance(ty, ir.TInt):
        lo, hi = int_range(kind if kind in INT_KINDS else "i32")
        return rng.choice([v for v in (0, 1, 2, 3, 7, 10, 100, 255, lo, lo + 1, hi, hi - 1, -1, -7) if lo <= v <= hi])
    if isinstance(ty, ir.TReal):
        return rng.choice([0, 1, -1, 2])
    if isinstance(ty, ir.TBool):
        return rng.random() < 0.5
    if isinstance(ty, ir.TStr):
        return rng.choice(["", "a", "ab", "hello"])
    if isinstance(ty, ir.TEnum):
        return rng.randrange(len(ty.members))
    if isinstance(ty, ir.TOption):
        return None if rng.random() < 0.3 else _sample(ty.inner, kind, rng, fe, depth)
    if isinstance(ty, ir.TList):
        return [_sample(ty.elem, kind, rng, fe, depth) for _ in range(rng.choice([0, 1, 2, 3]))]
    if isinstance(ty, ir.TDict):
        return {_sample(ty.key, None, rng, fe, depth): _sample(ty.val, kind, rng, fe, depth) for _ in range(rng.choice([0, 1, 2]))}
    if isinstance(ty, ir.TRecord):
        fields = {}
        for f, ft in ty.fields:
            fields[f] = rng.randrange(len(ft.members)) if f == "tag" and isinstance(ft, ir.TEnum) else _sample(ft, fe.slot_kind(ty.name, f), rng, fe, depth + 1)
        return {"__record__": ty.name, "fields": fields}
    if isinstance(ty, ir.TClass) and depth < 3 and ty.name in fe.classes:
        return {f: _sample(ft, fe.slot_kind(ty.name, f), rng, fe, depth + 1) for f, ft in fe.classes[ty.name].fields}
    raise ValueError(f"no sampler for {ty}")


@pytest.mark.skipif(not HAS_RUSTC, reason="rustc not available")
def test_proved_functions_hold_when_run(report):
    """Differential check of the model against rustc: every proved corpus
    function, run on sampled inputs that meet its preconditions, neither
    panics nor breaks its postconditions."""
    import random

    from telic.frontend.rust import RustFrontend
    from telic.frontend.rust_replay import run_rust_samples

    _, got = report
    fe = RustFrontend(str(CORPUS), CORPUS.read_text(), str(CORPUS))
    fe.run()
    infos = {i.key: i for i in fe.fns.values()}
    rng = random.Random(7)
    targets = []
    for name, want in expectations(CORPUS).items():
        f = got[name]
        if want != "proved" or f.status != "proved" or name not in infos:
            continue
        info = infos[name]
        fe._enter(info)
        try:
            models = [{p.name: _sample(p.ty, info.param_kinds.get(p.name) or info.elem_kinds.get(p.name), rng, fe) for p in f.fn.params} for _ in range(12)]
        except ValueError:
            continue
        targets.append((f.fn, models))
    outs = run_rust_samples(str(CORPUS), targets)
    assert outs is not None
    ran = len(outs)
    bad = []
    for fn, models in targets:
        for m, o in zip(models, outs.get(fn.name, [])):
            if "crash" in o or "violation" in o or "harness_error" in o:
                bad.append(f"{fn.name}{m}: {o}")
    assert ran >= 25, ran
    assert not bad, "\n".join(bad)
