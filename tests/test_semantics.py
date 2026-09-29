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
]


@pytest.mark.parametrize("e", VALUE_IDIOMS)
def test_python_value_idioms_match_cpython(e):
    """`x or default`, str and list `+`: values as CPython computes them."""
    src = f"def f(a: int, b: int) -> int:\n    return {e}\n"
    mod = lower_python("v.py", src)
    assert not mod.functions["f"].unsupported, (e, mod.functions["f"].unsupported)
    for a, b in INPUTS:
        assert model_value(mod, "f", a, b) == eval(e, {"a": a, "b": b}), (e, a, b)
