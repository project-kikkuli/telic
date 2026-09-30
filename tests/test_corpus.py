"""Every function in tests/cases/corpus.* must reach its expected verdict."""

import re
from pathlib import Path

import pytest

from telic.checker import CheckOptions, check

from conftest import needs_node

CASES = Path(__file__).parent / "cases"


def expectations(path: Path) -> dict[str, str]:
    out = {}
    lines = path.read_text().splitlines()
    for i, line in enumerate(lines):
        m = re.match(r"\s*(?:#|//) expect: (\w+)", line)
        if m:
            for nxt in lines[i + 1 :]:
                d = re.match(r"\s*(?:export\s+)?(?:def|function)\s+(\w+)", nxt)
                if d:
                    out[d.group(1)] = m.group(1)
                    break
    return out


def run(path: Path):
    rep = check([str(path)], CheckOptions(cache_path=None, lean=False), root=str(path.parent))
    return rep, {f.fn.name: f for f in rep.functions}


def verdict_table(rep, got, expect):
    rows = []
    for name, want in expect.items():
        f = got.get(name)
        have = f.status if f else "missing"
        if have != want:
            detail = [f"{v.ob.id}:{v.status}" for v in f.verdicts if v.status != "proved"] if f else []
            rows.append(f"{name}: expected {want}, got {have} {detail} {f.problems if f else ''}")
    return rows


@pytest.fixture(scope="module")
def python_corpus():
    return run(CASES / "corpus.py")


def test_python_corpus(python_corpus):
    path = CASES / "corpus.py"
    rep, got = python_corpus
    assert not [p for m in rep.modules for p in m.problems]
    bad = verdict_table(rep, got, expectations(path))
    assert not bad, "\n".join(bad)


def test_python_refutations_are_confirmed_by_execution(python_corpus):
    path = CASES / "corpus.py"
    _, got = python_corpus
    for name, want in expectations(path).items():
        if want != "refuted":
            continue
        vs = [v for v in got[name].verdicts if v.status == "refuted"]
        assert vs, name
        assert all(v.replay is not None and v.replay.confirmed for v in vs), name


@needs_node
def test_typescript_corpus():
    path = CASES / "corpus.ts"
    rep, got = run(path)
    assert not [p for m in rep.modules for p in m.problems], [p for m in rep.modules for p in m.problems]
    bad = verdict_table(rep, got, expectations(path))
    assert not bad, "\n".join(bad)


SUMS = """
def total(xs: list[int]) -> int:
    #@ requires all(x >= 0 for x in xs)
    #@ ensures result >= 0
    s = 0
    for x in xs:
        s += x
    return s


def halve(n: int) -> int:
    #@ requires n >= 0
    #@ ensures result * 2 <= n
    return n // 2 + 1
"""


def test_verdicts_do_not_depend_on_how_fast_the_solver_runs(tmp_path, monkeypatch):
    import time

    import z3

    (tmp_path / "sums.py").write_text(SUMS)

    def verdicts():
        rep = check([str(tmp_path / "sums.py")], CheckOptions(cache_path=None, lean=False, replay=False), root=str(tmp_path))
        return {f.fn.name: (f.status, sorted((v.ob.id, v.status) for v in f.verdicts)) for f in rep.functions}

    fast = verdicts()
    assert fast["total"][0] == "proved" and fast["halve"][0] == "refuted"
    # a loaded machine: stating the problem and solving it both take longer
    add, check_sat = z3.Solver.add, z3.Solver.check
    monkeypatch.setattr(z3.Solver, "add", lambda self, *a: (time.sleep(0.1), add(self, *a))[1])
    monkeypatch.setattr(z3.Solver, "check", lambda self, *a: (time.sleep(1), check_sat(self, *a))[1])
    assert verdicts() == fast
