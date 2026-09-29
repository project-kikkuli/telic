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
    out, owner, depth = {}, None, 0
    lines = path.read_text().splitlines()
    pending = None
    for line in lines:
        m = re.match(r"\s*impl\s+(\w+)\s*\{", line)
        if m:
            owner, depth = m.group(1), 0
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
            out[f"{owner}.{d.group(1)}" if owner else d.group(1)] = pending
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
