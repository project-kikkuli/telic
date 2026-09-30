"""Differential tests: telic's model of each language's arithmetic must agree
with the real interpreter on random expressions. If these fail, a proof could
be about a program that does not exist."""

import json
import os
import random
import subprocess
from fractions import Fraction

import pytest
import z3

from telic import logic as L
from telic.frontend.python import lower_python
from telic.program import Program
from telic.smt import Z3Encoder, to_python
from telic.vcgen import VCGen

from conftest import needs_node

N_EXPR = 120
INPUTS = [(a, b) for a in (-7, -3, -1, 0, 1, 2, 5, 9) for b in (-4, -2, -1, 1, 3, 7)]


def model_value(module, fname, a, b):
    program = Program.build([module])
    ref = program.resolve(module, fname)
    g = VCGen(program, ref, inputs={"a": L.IntV(a), "b": L.IntV(b)})
    g.definitional_mode = True
    g.run()
    (ex,) = [e for e in g.exits if e.value is not None]
    t = ex.value
    enc = Z3Encoder([])
    v = z3.simplify(enc.term(t))
    return to_python(v)


def py_expr(rnd, depth=0):
    if depth > 2 or rnd.random() < 0.25:
        return rnd.choice(["a", "b", str(rnd.randint(-5, 9))])
    x, y = py_expr(rnd, depth + 1), py_expr(rnd, depth + 1)
    return rnd.choice(
        [
            f"({x} + {y})",
            f"({x} - {y})",
            f"({x} * {y})",
            f"({x} // {y})",
            f"({x} % {y})",
            f"abs({x})",
            f"min({x}, {y})",
            f"max({x}, {y})",
            f"(-{x})",
            f"({x} if {x} < {y} else {y})",
            f"round({x} / {y})",
            f"int({x} / {y})",
            f"math.floor({x} / {y})",
            f"math.ceil({x} / {y})",
        ]
    )


def test_python_integer_semantics_match_cpython():
    import math

    rnd = random.Random(1234)
    checked = 0
    for k in range(N_EXPR):
        e = py_expr(rnd)
        src = f"import math\n\ndef f(a: int, b: int) -> int:\n    return {e}\n"
        mod = lower_python("gen.py", src)
        assert not mod.functions["f"].unsupported, (e, mod.functions["f"].unsupported)
        for a, b in rnd.sample(INPUTS, 6):
            try:
                expected = eval(e, {"math": math, "a": a, "b": b})
            except ZeroDivisionError:
                continue
            got = model_value(mod, "f", a, b)
            assert got == expected, f"{e} at a={a}, b={b}: model {got}, CPython {expected}"
            checked += 1
    assert checked > 300


def ts_expr(rnd, depth=0):
    if depth > 2 or rnd.random() < 0.25:
        return rnd.choice(["a", "b", str(rnd.randint(0, 9))])
    x, y = ts_expr(rnd, depth + 1), ts_expr(rnd, depth + 1)
    return rnd.choice(
        [
            f"({x} + {y})",
            f"({x} - {y})",
            f"({x} * {y})",
            f"({x} % {y})",
            f"Math.floor({x} / {y})",
            f"Math.trunc({x} / {y})",
            f"Math.round({x} / {y})",
            f"Math.ceil({x} / {y})",
            f"Math.abs({x})",
            f"Math.min({x}, {y})",
            f"Math.max({x}, {y})",
            f"(-{x})",
            f"({x} < {y} ? {x} : {y})",
        ]
    )


@needs_node
def test_javascript_semantics_match_node(tmp_path):
    from telic.frontend.typescript import lower_typescript_files

    rnd = random.Random(99)
    exprs = [ts_expr(rnd) for _ in range(N_EXPR)]
    files = []
    for i, e in enumerate(exprs):
        p = tmp_path / f"e{i}.ts"
        p.write_text(
            "export function f(a: number, b: number): number {\n"
            "  //@ requires Number.isInteger(a) && Number.isInteger(b)\n"
            f"  return {e};\n}}\n"
        )
        files.append(str(p))
    mods = lower_typescript_files(files, str(tmp_path))
    # Ask node for the real values in one process.
    cases = [(i, a, b) for i in range(len(exprs)) for a, b in rnd.sample(INPUTS, 5)]
    js = "const out = [];\n" + "\n".join(
        f"out.push((function(a, b) {{ return {exprs[i]}; }})({a}, {b}));" for i, a, b in cases
    ) + "\nconsole.log(JSON.stringify(out.map(x => Number.isFinite(x) ? x : null).map(x => Object.is(x, -0) ? 0 : x)));"
    real = json.loads(subprocess.run(["node", "-e", js], capture_output=True, text=True, check=True).stdout)
    checked = 0
    for (i, a, b), expected in zip(cases, real):
        if expected is None:  # NaN / Infinity: a division by zero telic reports separately
            continue
        mod = mods[files[i]]
        assert not mod.functions["f"].unsupported, (exprs[i], mod.functions["f"].unsupported)
        got = model_value(mod, "f", a, b)
        if isinstance(got, str):
            continue  # an intermediate division by zero: undefined in the model (and flagged)
        if isinstance(got, Fraction):
            got = float(got)
        assert got == expected, f"{exprs[i]} at a={a}, b={b}: model {got}, node {expected}"
        checked += 1
    assert checked > 300


def test_python_float_rounding_model():
    """round() is banker's rounding on exact halves; our model agrees."""
    src = "def f(a: int, b: int) -> int:\n    return round(a / b)\n"
    mod = lower_python("r.py", src)
    for a in range(-11, 12):
        for b in (1, 2, 4):
            assert model_value(mod, "f", a, b) == round(a / b), (a, b)


VALUE_IDIOMS = [
    "(a or b)",
    "(a and b)",
    "(a or b or 3)",
    "len(('x' if a > 0 else '') + ('yz' if b > 0 else ''))",
    "len(('x' if a > 0 else '') or 'yy')",
    "len([a, b] + [a])",
    "len([a] + [])",
    "((a if a > 1 else None) or b)",
    "(1 if (a > 0 and 'q' or '') else 0)",
    "len([0] * a)",
    "len(b * [a, b])",
    "len(range(a))",
    "len(range(b, a))",
    "len(list(range(a, 4)))",
    "len([x * 2 for x in range(b, a)])",
]


@pytest.mark.parametrize("e", VALUE_IDIOMS)
def test_python_value_idioms_match_cpython(e):
    """`x or default`, str and list `+`: values as CPython computes them."""
    src = f"def f(a: int, b: int) -> int:\n    return {e}\n"
    mod = lower_python("v.py", src)
    assert not mod.functions["f"].unsupported, (e, mod.functions["f"].unsupported)
    for a, b in INPUTS:
        assert model_value(mod, "f", a, b) == eval(e, {"a": a, "b": b}), (e, a, b)


OPAQUE_IDIOMS = [("x == 'a'", str), ("x != 'a'", str), ("x == 'b' or x == 'a'", str), ("x > 3", int), ("x <= b", int), ("x == 2", int), ("x != b", int)]
OPAQUE_INPUTS = ["a", "b", "", 2, 3, 5, -1]


def forced_value(module, fname, x, b):
    """What the model says ``fname(x, b)`` returns, given only what telic
    knows about ``x`` as an unchecked value (its type and its value)."""
    program = Program.build([module])
    ref = program.resolve(module, fname)
    kind, lit = ("str", L.StrV(x)) if isinstance(x, str) else ("int", L.IntV(x))
    boxed = L.Fn(f"box.{kind}", (lit,), L.OPAQUE)
    g = VCGen(program, ref, inputs={"x": boxed, "b": L.IntV(b)})
    g.definitional_mode = True
    g.run()
    (ex,) = [e for e in g.exits if e.value is not None]
    known = [L.eq(L.Fn(f"unbox.{kind}.", (boxed,), lit.sort), lit), L.Fn("opaque.isinstance.Bool", (boxed, L.StrV(kind)), L.BOOL)]
    enc = Z3Encoder([])
    out = []
    for guess in (True, False):
        s = z3.Solver(ctx=enc.ctx)
        for f in known + g.lemmas + ex.facts:
            s.add(enc.term(f))
        s.add(enc.term(L.eq(ex.value, L.BoolV(guess))))
        if s.check() != z3.unsat:
            out.append(guess)
    return out


@pytest.mark.parametrize("e,same", OPAQUE_IDIOMS)
def test_python_unchecked_comparisons_match_cpython(e, same):
    """An unchecked value compared with a string or an int: the model forces
    CPython's answer when the types match, and never the opposite one."""
    src = f"from typing import Any\n\ndef f(x: Any, b: int) -> bool:\n    return {e}\n"
    mod = lower_python("o.py", src)
    for x in OPAQUE_INPUTS:
        for b in (0, 2, 4):
            try:
                want = eval(e, {"x": x, "b": b})
            except TypeError:
                continue
            got = forced_value(mod, "f", x, b)
            assert want in got, (e, x, b, got)
            if type(x) is same:
                assert got == [want], (e, x, b, got)


LIST_IDIOMS = ["([a, b] * 3)[4]", "([7] * a)[a - 1]", "[i * i for i in range(b, 9)][2]", "list(range(a, b + 12))[3]", "(b * [a, 5])[b + 1]"]


@pytest.mark.parametrize("e", LIST_IDIOMS)
def test_python_built_lists_match_cpython(e):
    """range(), list(), [..] * n and comprehensions over them: the facts the
    model states pin each element to what CPython computes."""
    src = f"def f(a: int, b: int) -> int:\n    return {e}\n"
    mod = lower_python("v.py", src)
    assert not mod.functions["f"].unsupported, (e, mod.functions["f"].unsupported)
    program = Program.build([mod])
    ref = program.resolve(mod, "f")
    for a, b in INPUTS:
        try:
            want = eval(e, {"a": a, "b": b})
        except IndexError:
            continue
        g = VCGen(program, ref, inputs={"a": L.IntV(a), "b": L.IntV(b)})
        g.definitional_mode = True
        g.run()
        (ex,) = [x for x in g.exits if x.value is not None]
        enc = Z3Encoder([])
        s = z3.Solver(ctx=enc.ctx)
        for f in g.lemmas + ex.facts:
            s.add(enc.term(f))
        s.add(z3.Not(enc.term(L.eq(ex.value, L.IntV(want)))))
        assert s.check() == z3.unsat, (e, a, b, want)
