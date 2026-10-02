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


@pytest.mark.parametrize("variable", ["TELIC_Z3", "TELIC_LEAN", "TELIC_CORE"])
def test_toolchain_receipts_bind_solver_overrides(tmp_path, monkeypatch, variable):
    import telic.checker as checker

    for name in ("TELIC_Z3", "TELIC_LEAN", "TELIC_CORE"):
        monkeypatch.delenv(name, raising=False)
    monkeypatch.setattr(checker, "_TOOLCHAIN", None)
    original = checker.toolchain_id()
    executable = tmp_path / variable.lower()
    executable.write_text("#!/bin/sh\nprintf '%s\\n' override\n")
    executable.chmod(0o755)
    monkeypatch.setenv(variable, str(executable))
    monkeypatch.setattr(checker, "_TOOLCHAIN", None)
    assert checker.toolchain_id() != original


def test_each_check_refreshes_selected_tool_identity(tmp_path, monkeypatch):
    monkeypatch.delenv("TELIC_LEAN", raising=False)
    opts = CheckOptions(cache_path=str(tmp_path / ".telic/cache.json"), lean=False)
    solved = []
    for version in ("lean-a", "lean-b"):
        executable = tmp_path / version
        executable.write_text(f"#!/bin/sh\nprintf '%s\\n' {version}\n")
        executable.chmod(0o755)
        monkeypatch.setenv("TELIC_LEAN", str(executable))
        solved.append(run(tmp_path, SRC).solved)
    assert solved[0] > 0 and solved[1] == solved[0]


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


INVARIANT_CONSTANT = """
MINIMUM = {minimum}

class Box:
    #@ invariant self.value >= MINIMUM
    def __init__(self, value: int):
        self.value = value

def read(box: Box) -> int:
    #@ ensures result >= 0
    return box.value
"""


OVERRIDE_ENTRY = """class Base:
    def __init__(self, x: int):
        self.x = x
{base_method}
class Sub(Base):
    #@ invariant self.x >= 0
    def m(self) -> int:
        #@ ensures result >= 0
        return self.x
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


@pytest.mark.parametrize("engine", ["python", "ox"])
def test_a_class_invariant_constant_change_invalidates_function_receipt(tmp_path, engine):
    if engine == "ox" and binary() is None:
        pytest.skip("telic-core not built")
    opts = CheckOptions(cache_path=str(tmp_path / ".telic/cache.json"), lean=False, engine=engine)
    statuses = []
    for minimum in (0, -1):
        (tmp_path / "m.py").write_text(INVARIANT_CONSTANT.format(minimum=minimum))
        rep = check([str(tmp_path / "m.py")], opts, root=str(tmp_path))
        read = next(f for f in rep.functions if f.fn.name == "read")
        statuses.append((read.status, read.from_receipt))
    assert statuses == [("proved", False), ("refuted", False)]


@pytest.mark.parametrize("engine", ["python", "ox"])
def test_adding_an_ancestor_override_invalidates_untrusted_entry_receipt(tmp_path, engine):
    if engine == "ox" and binary() is None:
        pytest.skip("telic-core not built")
    opts = CheckOptions(cache_path=str(tmp_path / ".telic/cache.json"), lean=False, replay=False, infer=False, engine=engine)
    added = "    def m(self) -> int:\n        self.x = -1\n        return self.x\n"
    statuses = []
    for method in ("", added):
        (tmp_path / "m.py").write_text(OVERRIDE_ENTRY.format(base_method=method))
        rep = check([str(tmp_path / "m.py")], opts, root=str(tmp_path))
        child = next(f for f in rep.functions if f.fn.name == "Sub.m")
        statuses.append((child.status, child.from_receipt))
    assert statuses == [("proved", False), ("refuted", False)]


def test_functions_calling_each_other_keep_their_own_verdicts(tmp_path):
    # they depend on the same functions, but each has its own receipt and inference
    src = "def ping(n: int) -> int:\n    #@ requires n >= 0\n    #@ ensures result == 0\n    if n == 0:\n        return 0\n    return pong(n - 1)\n\n\ndef pong(n: int) -> int:\n    #@ requires n >= 0\n    #@ ensures result == 1\n    if n == 0:\n        return 0\n    return ping(n - 1)\n"
    first = {f.fn.name: (f.status, f.inferred.measure) for f in run(tmp_path, src).functions}
    assert first["ping"][0] != "refuted" and first["pong"] == ("refuted", "n")
    assert {f.fn.name: (f.status, f.inferred.measure) for f in run(tmp_path, src).functions} == first
