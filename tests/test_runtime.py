import subprocess
import sys
import textwrap

import pytest

from telic.runtime import ContractViolation, load_instrumented


def write(tmp_path, src):
    p = tmp_path / "m.py"
    p.write_text(textwrap.dedent(src))
    return str(p)


def test_requires_and_ensures_are_enforced(tmp_path):
    m = load_instrumented(write(tmp_path, """
        def half(n: int) -> int:
            #@ requires n % 2 == 0
            #@ ensures result * 2 == n
            return n // 2 + (1 if n > 100 else 0)
    """), "m1")
    assert m.half(4) == 2
    with pytest.raises(ContractViolation) as e:
        m.half(3)
    assert e.value.kind == "requires"
    with pytest.raises(ContractViolation) as e:
        m.half(102)
    assert e.value.kind == "ensures"


def test_old_and_scalar_params_see_entry_values(tmp_path):
    m = load_instrumented(write(tmp_path, """
        def bump(xs: list[int], n: int) -> int:
            #@ ensures len(xs) == len(old(xs)) + 1
            #@ ensures result == n
            xs.append(n)
            k = n
            n = 0
            return k
    """), "m2")
    assert m.bump([1], 5) == 5


def test_loop_invariants_are_checked(tmp_path):
    m = load_instrumented(write(tmp_path, """
        def f(n: int) -> int:
            s = 0
            #@ invariant s <= 3
            for i in range(n):
                s += 1
            return s
    """), "m3")
    assert m.f(3) == 3
    with pytest.raises(ContractViolation) as e:
        m.f(5)
    assert e.value.kind == "invariant"


def test_assert_comments_are_checked(tmp_path):
    m = load_instrumented(write(tmp_path, """
        def f(x: int) -> int:
            y = x - 1
            #@ assert y < x
            #@ assert y > 0
            return y
    """), "m4")
    assert m.f(5) == 4
    with pytest.raises(ContractViolation):
        m.f(0)


def test_telic_run_command(tmp_path):
    p = write(tmp_path, """
        def f(x: int) -> int:
            #@ requires x > 0
            return x

        print(f(1))
        f(-1)
    """)
    out = subprocess.run([sys.executable, "-m", "telic", "run", p], capture_output=True, text=True)
    assert out.returncode == 1
    assert "1" in out.stdout and "@requires x > 0" in out.stderr


def test_pytest_plugin_enforces_contracts(tmp_path):
    (tmp_path / "lib.py").write_text("def inc(x: int) -> int:\n    #@ ensures result > x\n    return x if x > 10 else x + 1\n")
    (tmp_path / "test_lib.py").write_text("from lib import inc\n\ndef test_small():\n    assert inc(1) == 2\n\ndef test_big():\n    inc(11)\n")
    out = subprocess.run([sys.executable, "-m", "pytest", "-q", "-p", "telic.pytest_plugin", str(tmp_path)], capture_output=True, text=True, cwd=tmp_path)
    assert "1 failed, 1 passed" in out.stdout, out.stdout
    assert "@ensures result > x" in out.stdout


LISTED = """
    from enum import Enum


    class Status(Enum):
        OPEN = 1
        DONE = 2


    class Task:
        #@ invariant self.left >= 0
        #@ lifecycle status: Status.OPEN -> Status.DONE

        def __init__(self, left: int, status: Status):
            #@ requires left >= 0
            self.left = left
            self.status = status


    def reopen(ts: list[Task]) -> None:
        for t in ts:
            t.status = Status.OPEN


    def drain(ts: list[Task]) -> None:
        for t in ts:
            t.left = -1
"""


@pytest.mark.parametrize(
    "call,kind",
    [
        ("m.reopen([m.Task(-1, m.Status.OPEN)])", "requires"),  # an object handed in must satisfy its invariants
        ("m.reopen([m.Task(1, m.Status.DONE)])", "lifecycle"),
        ("m.drain([m.Task(1, m.Status.OPEN)])", "class.inv"),
    ],
)
def test_objects_in_a_list_are_checked_like_objects(tmp_path, call, kind):
    m = load_instrumented(write(tmp_path, LISTED), "m_listed")
    bad = m.Task.__new__(m.Task)
    object.__setattr__(bad, "left", -1)
    object.__setattr__(bad, "status", m.Status.OPEN)
    call = call.replace("m.Task(-1, m.Status.OPEN)", "bad")
    with pytest.raises(ContractViolation) as e:
        eval(call, {"m": m, "bad": bad})
    assert e.value.kind == kind
    m.reopen([m.Task(1, m.Status.OPEN)])
