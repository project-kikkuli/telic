"""Proofs are cached by formula, so edits re-verify only what they touch."""

from pathlib import Path

import pytest

from telic.checker import CheckOptions, check, obligation_key
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


def test_mathematical_receipts_survive_an_unrelated_kernel_fingerprint_change(tmp_path, monkeypatch):
    import telic.checker as checker

    (tmp_path / "m.py").write_text(SRC)
    opts = CheckOptions(cache_path=str(tmp_path / ".telic/cache.json"), receipts=False, infer=False, lean=False)
    monkeypatch.setattr(checker, "toolchain_id", lambda: "kernel-a")
    first = check([str(tmp_path / "m.py")], opts, root=str(tmp_path))
    monkeypatch.setattr(checker, "toolchain_id", lambda: "kernel-b")
    second = check([str(tmp_path / "m.py")], opts, root=str(tmp_path))
    assert first.solved > 0 and second.solved == 0
    assert second.cache_hits >= first.solved


def test_mathematical_receipts_bind_resource_budget(tmp_path):
    (tmp_path / "m.py").write_text(SRC)
    path = str(tmp_path / ".telic/cache.json")
    first = check([str(tmp_path / "m.py")], CheckOptions(cache_path=path, receipts=False, infer=False, lean=False, rlimit=2_000_000), root=str(tmp_path))
    second = check([str(tmp_path / "m.py")], CheckOptions(cache_path=path, receipts=False, infer=False, lean=False, rlimit=1_900_000), root=str(tmp_path))
    assert first.solved > 0 and second.solved > 0


def test_mathematical_receipts_bind_timeout_budget(tmp_path):
    (tmp_path / "m.py").write_text(SRC)
    path = str(tmp_path / ".telic/cache.json")
    first = check([str(tmp_path / "m.py")], CheckOptions(cache_path=path, receipts=False, infer=False, lean=False, timeout_ms=60000), root=str(tmp_path))
    second = check([str(tmp_path / "m.py")], CheckOptions(cache_path=path, receipts=False, infer=False, lean=False, timeout_ms=59000), root=str(tmp_path))
    assert first.solved > 0 and second.solved > 0


def test_mathematical_receipts_bind_selected_python_z3_library(tmp_path, monkeypatch):
    import telic.toolchain as toolchain

    (tmp_path / "m.py").write_text(SRC)
    opts = CheckOptions(cache_path=str(tmp_path / ".telic/cache.json"), receipts=False, infer=False, lean=False)
    monkeypatch.setattr(toolchain, "python_z3", lambda: ("z3", "library-a"))
    first = check([str(tmp_path / "m.py")], opts, root=str(tmp_path))
    monkeypatch.setattr(toolchain, "python_z3", lambda: ("z3", "library-b"))
    second = check([str(tmp_path / "m.py")], opts, root=str(tmp_path))
    assert first.solved > 0 and second.solved > 0


def test_native_mathematical_receipts_bind_selected_z3_executable(tmp_path, monkeypatch):
    if binary() is None:
        pytest.skip("telic-core not built")
    import telic.toolchain as toolchain

    path = tmp_path / "m.py"
    path.write_text("def m(x: int) -> int:\n    #@ requires x >= 0\n    #@ ensures result >= x\n    return x + 1\n")
    options = CheckOptions(cache_path=str(tmp_path / ".telic/cache.json"), receipts=False, infer=False, lean=False, engine="ox", replay=False)
    monkeypatch.setattr(toolchain, "native_z3", lambda: ("z3", "executable-a"))
    first = check([str(path)], options, root=str(tmp_path))
    monkeypatch.setattr(toolchain, "native_z3", lambda: ("z3", "executable-b"))
    second = check([str(path)], options, root=str(tmp_path))
    assert first.solved > 0 and second.solved > 0


def test_mathematical_receipts_bind_unused_parameter_signature(tmp_path):
    path = tmp_path / "m.py"
    cache = str(tmp_path / ".telic/cache.json")
    options = CheckOptions(cache_path=cache, receipts=False, infer=False, lean=False)
    path.write_text("def m(x: int) -> int:\n    #@ ensures result == 0\n    return 0\n")
    first = check([str(path)], options, root=str(tmp_path))
    path.write_text("def m(x: bool) -> int:\n    #@ ensures result == 0\n    return 0\n")
    second = check([str(path)], options, root=str(tmp_path))
    assert first.solved > 0 and second.solved > 0


@pytest.mark.parametrize("engine", ["python", "ox"])
def test_mathematical_receipts_bind_unused_record_field_sorts(tmp_path, engine):
    if engine == "ox" and binary() is None:
        pytest.skip("telic-core not built")
    path = tmp_path / "m.py"
    cache = str(tmp_path / ".telic/cache.json")
    options = CheckOptions(cache_path=cache, receipts=False, infer=False, lean=False, engine=engine, replay=False)
    prefix = "class Box:\n    def __init__(self):\n        self.value: int = 0\n"
    suffix = "\ndef read(box: Box) -> int:\n    #@ ensures result == 0\n    return 0\n"
    path.write_text(prefix + "        self.unused: int = 1\n" + suffix)
    first = check([str(path)], options, root=str(tmp_path))
    path.write_text(prefix + "        self.unused: bool = True\n" + suffix)
    second = check([str(path)], options, root=str(tmp_path))
    read = next(f for f in second.functions if f.fn.name == "read")
    assert first.solved > 0 and any(v.method == "z3" for v in read.verdicts)


def test_mathematical_receipts_bind_reachable_theory_axioms():
    from telic import ir, logic as L
    from telic.checker import Theory
    from telic.vcgen import Obligation

    call = L.Fn("f", (L.ONE,), L.INT)
    ob = Obligation(id="axiom", func="f", kind="test", loc=ir.Loc(1), site=None, message="", hyps=[], goal=L.eq(call, L.ONE))
    positive = Theory(axioms=[L.Axiom("f_rule", L.eq(call, L.ONE), "", symbol="f")])
    negative = Theory(axioms=[L.Axiom("f_rule", L.eq(call, L.ZERO), "", symbol="f")])
    assert obligation_key(ob, positive, 2_000_000) != obligation_key(ob, negative, 2_000_000)


def test_unknown_solver_results_are_not_persisted_as_math_receipts(tmp_path, monkeypatch):
    import telic.checker as checker
    from telic.smt import SmtResult

    (tmp_path / "m.py").write_text(SRC)
    cache_path = tmp_path / ".telic/cache.json"
    options = CheckOptions(cache_path=str(cache_path), receipts=False, infer=False, lean=False, replay=False)
    monkeypatch.setattr(checker, "solve_all", lambda obs, *args: [SmtResult("unknown", 0.0, reason="resource limit") for _ in obs])
    first = check([str(tmp_path / "m.py")], options, root=str(tmp_path))
    second = check([str(tmp_path / "m.py")], options, root=str(tmp_path))
    assert first.solved > 0 and second.solved == first.solved
    assert all(value.get("method") != "unknown" for value in checker.ProofCache(str(cache_path)).data.values())


def test_lean_receipts_have_a_separate_statement_and_solver_key():
    from telic.lean import _lean_receipt_key

    first = _lean_receipt_key("statement-a", ("Lean 4", "binary-a"))
    assert first.startswith("lean:")
    assert first != _lean_receipt_key("statement-b", ("Lean 4", "binary-a"))
    assert first != _lean_receipt_key("statement-a", ("Lean 4", "binary-b"))


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


def test_python_z3_identity_hashes_loaded_library(monkeypatch, tmp_path):
    import hashlib
    import z3.z3core as z3core

    from telic.toolchain import python_z3

    loaded = z3core.Z3_get_version.__defaults__[0].f._objects["0"]
    monkeypatch.setattr(z3core, "_z3_lib_resource_path", str(tmp_path))
    assert python_z3()[1] == hashlib.sha256(Path(loaded._name).read_bytes()).hexdigest()


def test_lean_replacement_keeps_mathematical_receipts(tmp_path, monkeypatch):
    monkeypatch.delenv("TELIC_LEAN", raising=False)
    opts = CheckOptions(cache_path=str(tmp_path / ".telic/cache.json"), lean=False)
    solved = []
    for version in ("lean-a", "lean-b"):
        executable = tmp_path / version
        executable.write_text(f"#!/bin/sh\nprintf '%s\\n' {version}\n")
        executable.chmod(0o755)
        monkeypatch.setenv("TELIC_LEAN", str(executable))
        solved.append(run(tmp_path, SRC).solved)
    assert solved[0] > 0 and solved[1] == 0


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
    for method in ("\n\n\n", added):
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
