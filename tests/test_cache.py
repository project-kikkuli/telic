"""Proofs are cached by formula, so edits re-verify only what they touch."""

import pytest

from telic.checker import CheckOptions, check
from telic.engine import binary

SRC = """
def a(x: int) -> int:
    #@ requires x >= 0
    #@ ensures result >= 0
    return x * 2


def b(x: int) -> int:
    #@ requires x >= 0
    #@ ensures result >= x
    return x + 1


def c(x: int) -> int:
    #@ requires x >= 0
    #@ ensures result >= 1
    return b(x)
"""


def run(tmp_path, src):
    (tmp_path / "m.py").write_text(src)
    return check([str(tmp_path / "m.py")], CheckOptions(cache_path=str(tmp_path / ".telic/cache.json")), root=str(tmp_path))


def test_second_run_is_fully_cached(tmp_path):
    r1 = run(tmp_path, SRC)
    r2 = run(tmp_path, SRC)
    assert r1.solved > 0 and r2.solved == 0 and r2.cache_hits == r1.cache_hits + r1.solved


def test_editing_a_body_rechecks_only_that_body(tmp_path):
    run(tmp_path, SRC)
    r = run(tmp_path, SRC.replace("return x * 2", "return x * 3"))
    solved = {v.ob.func.split("::")[1] for f in r.functions for v in f.verdicts if v.method == "z3"}
    assert solved == {"a"}


def test_editing_a_contract_rechecks_callers(tmp_path):
    run(tmp_path, SRC)
    r = run(tmp_path, SRC.replace("#@ ensures result >= x\n", "#@ ensures result >= x + 1\n"))
    solved = {v.ob.func.split("::")[1] for f in r.functions for v in f.verdicts if v.method == "z3"}
    assert solved == {"b", "c"}


OUTSIDE = """
LIMIT = 5


class Box:
    #@ invariant self.v >= 0

    def __init__(self):
        self.v: int = 0


def read(b: Box) -> int:
    #@ ensures result >= 0
    return b.v


def lim() -> int:
    #@ ensures result <= 5
    return LIMIT
"""


@pytest.mark.parametrize("engine", ["python", "ox"])
@pytest.mark.parametrize("old,new,fn", [("self.v >= 0", "self.v >= -5", "read"), ("LIMIT = 5", "LIMIT = 10", "lim")])
def test_an_edit_outside_a_function_rechecks_it(tmp_path, engine, old, new, fn):
    if engine == "ox" and binary() is None:
        pytest.skip("telic-core not built")
    opts = CheckOptions(cache_path=str(tmp_path / ".telic/cache.json"), lean=False, engine=engine)
    for src, want in ((OUTSIDE, "proved"), (OUTSIDE.replace(old, new), "refuted")):
        (tmp_path / "m.py").write_text(src)
        rep = check([str(tmp_path / "m.py")], opts, root=str(tmp_path))
        assert {f.fn.name: f.status for f in rep.functions}[fn] == want
