"""Differential tests: telic's model of each language's arithmetic must agree
with the real interpreter on random expressions. If these fail, a proof could
be about a program that does not exist."""

import json
import math
import os
import random
import shutil
import struct
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


def model_value_one(module, fname, x, sort=L.FLOAT64):
    program = Program.build([module])
    ref = program.resolve(module, fname)
    g = VCGen(program, ref, inputs={"x": L.fval(x, sort)})
    g.definitional_mode = True
    g.run()
    (ex,) = [e for e in g.exits if e.value is not None]
    enc = Z3Encoder([])
    return to_python(z3.simplify(enc.term(ex.value)))


def test_array_lambda_projection_is_capture_safe_and_matches_python():
    binder = L.Const("index", L.INT)
    outer = L.Const("outer", L.INT)
    projection = L.array_lambda(binder, L.add(binder, outer))
    assert L.consts(projection) == {outer}

    alpha_name = L.Const("index$alpha", L.INT)
    substituted = L.substitute(projection, {outer: binder, alpha_name: L.IntV(7)})
    assert isinstance(substituted, L.ArrayLambda)
    assert substituted.binder != binder
    assert L.consts(substituted) == {binder}

    enc = Z3Encoder([])
    selected = enc.term(L.select(substituted, L.IntV(3)))
    solver = z3.Solver(ctx=enc.ctx)
    solver.add(selected != enc.term(L.add(L.IntV(3), binder)))
    assert solver.check() == z3.unsat

    quantified = L.Quant("forall", (binder,), L.gt(binder, outer), patterns=((binder,),))
    renamed = L.substitute(quantified, {outer: binder, alpha_name: L.IntV(7)})
    assert isinstance(renamed, L.Quant)
    assert renamed.vars[0] != binder
    assert renamed.patterns == ((renamed.vars[0],),)

    from telic.lean import LeanPrinter, Namer

    rendered = LeanPrinter(Namer(), {}).t(projection)
    assert "fun" in rendered and "index" in rendered
    free_bool = L.Const("shadow", L.BOOL)
    shadowed = L.array_lambda(L.Const("shadow", L.INT), L.ite(free_bool, L.ONE, L.ZERO))
    namer = Namer()
    free_name = namer(free_bool.name)
    shadowed_text = LeanPrinter(namer, {}).t(shadowed)
    assert f"{free_name} : Prop" not in shadowed_text
    assert f"{free_name}" in shadowed_text and "fun (shadow_2 : Int)" in shadowed_text


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


@needs_node
def test_javascript_decimal_literals_round_once_like_node(tmp_path):
    from telic.frontend.typescript import lower_typescript

    literal = "1.000000000000000300000000000000000000000000000000000000000000000000001"
    source = f"export function f(): number {{ return {literal}; }}\n"
    path = tmp_path / "wide_literal.ts"
    path.write_text(source)
    mod = lower_typescript(str(path), source, root=str(tmp_path))
    program = Program.build([mod])
    ref = program.resolve(mod, "f")
    g = VCGen(program, ref)
    g.definitional_mode = True
    g.run()
    (ex,) = [e for e in g.exits if e.value is not None]
    actual = to_python(z3.simplify(Z3Encoder([]).term(ex.value)))
    expected = float(subprocess.run(["node", "-e", f"console.log({literal})"], capture_output=True, text=True, check=True).stdout)
    assert actual == expected == 1.0000000000000002


@needs_node
def test_javascript_math_rounding_matches_node(tmp_path):
    from telic.frontend.typescript import lower_typescript_files

    inputs = [-0.0, 0.0, -0.25, -0.5, -0.75, 0.25, 0.5, 0.75, -1.5, 1.5, 2**52 + 0.5, float("nan"), float("inf"), -float("inf")]
    funcs = ["floor", "ceil", "trunc", "round"]
    files = []
    for name in funcs:
        p = tmp_path / f"math_{name}.ts"
        p.write_text(f"export function f(x: number): number {{ return Math.{name}(x); }}\n")
        files.append(str(p))
    mods = lower_typescript_files(files, str(tmp_path))
    encoded_inputs = [
        "NaN" if math.isnan(x) else "Infinity" if x == float("inf") else "-Infinity" if x == float("-inf")
        else "-0" if x == 0.0 and math.copysign(1.0, x) < 0 else repr(x)
        for x in inputs
    ]
    js = "const xs = [" + ", ".join(encoded_inputs) + "];\n"
    js += "const enc = x => Number.isNaN(x) ? 'NaN' : x === Infinity ? '+Inf' : x === -Infinity ? '-Inf' : Object.is(x, -0) ? '-0' : String(x);\n"
    js += "console.log(JSON.stringify(xs.map(x => [Math.floor(x), Math.ceil(x), Math.trunc(x), Math.round(x)].map(enc))));"
    expected = json.loads(subprocess.run(["node", "-e", js], capture_output=True, text=True, check=True).stdout)
    for op_i, name in enumerate(funcs):
        mod = mods[files[op_i]]
        assert not mod.functions["f"].unsupported, mod.functions["f"].unsupported
        for value, row in zip(inputs, expected):
            got = model_value_one(mod, "f", value)
            want = row[op_i]
            if want == "NaN":
                assert math.isnan(got), (name, value, got, want)
            elif want == "+Inf":
                assert got == float("inf"), (name, value, got, want)
            elif want == "-Inf":
                assert got == float("-inf"), (name, value, got, want)
            elif want == "-0":
                assert got == 0.0 and math.copysign(1.0, got) < 0, (name, value, got, want)
            else:
                assert got == float(want), (name, value, got, want)


@needs_node
def test_javascript_math_min_max_nan_and_signed_zero_match_node(tmp_path):
    from telic.frontend.typescript import lower_typescript

    source = """export function f(a: number, b: number): number { return Math.min(a, b); }
export function g(a: number, b: number): number { return Math.max(a, b); }
"""
    path = tmp_path / "math_min_max.ts"
    path.write_text(source)
    mod = lower_typescript(str(path), source, root=str(tmp_path))
    vectors = [(float("nan"), 1.0), (-0.0, 0.0), (0.0, -0.0), (float("inf"), -float("inf"))]
    for name, op in (("f", "min"), ("g", "max")):
        for a, b in vectors:
            program = Program.build([mod])
            ref = program.resolve(mod, name)
            gvc = VCGen(program, ref, inputs={"a": L.fval(a, L.FLOAT64), "b": L.fval(b, L.FLOAT64)})
            gvc.definitional_mode = True
            gvc.run()
            (ex,) = [e for e in gvc.exits if e.value is not None]
            got = to_python(z3.simplify(Z3Encoder([]).term(ex.value)))
            js_values = ["NaN" if math.isnan(x) else "Infinity" if x == math.inf else "-Infinity" if x == -math.inf else "-0" if x == 0 and math.copysign(1.0, x) < 0 else repr(x) for x in (a, b)]
            expected = subprocess.run(["node", "-e", f"const x=Math.{op}({js_values[0]},{js_values[1]}); console.log(Number.isNaN(x)?'NaN':Object.is(x,-0)?'-0':String(x))"], capture_output=True, text=True, check=True).stdout.strip()
            if expected == "NaN":
                assert math.isnan(got), (op, a, b, got)
            elif expected == "-0":
                assert got == 0.0 and math.copysign(1.0, got) < 0, (op, a, b, got)
            else:
                assert got == float(expected), (op, a, b, got, expected)


def test_python_float_rounding_model():
    """round() is banker's rounding on exact halves; our model agrees."""
    src = "def f(a: int, b: int) -> int:\n    return round(a / b)\n"
    mod = lower_python("r.py", src)
    for a in range(-11, 12):
        for b in (1, 2, 4):
            assert model_value(mod, "f", a, b) == round(a / b), (a, b)


def test_python_float_sum_matches_target_interpreter():
    vectors = (
        [1e16, 1.0, -1e16], [1e16, -1e16, 1.0], [1.25, 2.5, -0.75],
        [1e100, 1.0, -1e100], [1e308, 1e308], [1e308, -1e308], [-0.0],
    )
    for xs in vectors:
        literals = ", ".join(repr(x) for x in xs)
        mod = lower_python("sum_float.py", f"def f() -> float:\n    xs: list[float] = [{literals}]\n    return sum(xs)\n")
        assert not mod.functions["f"].unsupported, mod.functions["f"].unsupported
        program = Program.build([mod])
        ref = program.resolve(mod, "f")
        from telic.checker import build_theory

        theory, _ = build_theory(program, {})
        g = VCGen(program, ref)
        g.definitional_mode = True
        g.run()
        (ex,) = [e for e in g.exits if e.value is not None]
        enc = Z3Encoder(list(theory.fundefs.values()))
        tagged = to_python(z3.simplify(enc.term(ex.value)))
        fields = next(iter(tagged.values()))
        assert fields[0] is False, (xs, tagged)
        actual = fields[2]
        expected = sum(xs)
        assert (math.isnan(actual) if math.isnan(expected) else actual == expected), (xs, actual, expected)


def test_python_integer_division_rounds_exact_quotient_like_cpython():
    cases = ((0, -1), (1, -2), (-1, 2), (-1, 10**400), (10**400, 10**400))
    for a, b in cases:
        mod = lower_python("int_division.py", "def f(a: int, b: int) -> float:\n    return a / b\n")
        program = Program.build([mod])
        ref = program.resolve(mod, "f")
        g = VCGen(program, ref, inputs={"a": L.IntV(a), "b": L.IntV(b)})
        g.definitional_mode = True
        g.run()
        (ex,) = [e for e in g.exits if e.value is not None]
        from telic.vcgen import as_py_number, sort_of

        tagged = L.mkrec(sort_of(mod.functions["f"].ret), as_py_number(ex.value).parts())
        raw = to_python(z3.simplify(Z3Encoder([]).term(tagged)))
        fields = next(iter(raw.values()))
        assert fields[0] is False
        actual = fields[2]
        expected = a / b
        assert actual == expected, (a, b, actual, expected)
        assert math.copysign(1.0, actual) == math.copysign(1.0, expected), (a, b, actual, expected)


def test_python_sum_keeps_integer_prefix_through_identity_comprehension():
    huge = "9" * 400
    src = f"def f() -> float:\n    xs = [{huge}, -{huge}, 0.0]\n    return sum([x for x in xs])\n"
    mod = lower_python("mixed_sum_comp.py", src)
    assert not mod.functions["f"].unsupported, mod.functions["f"].unsupported
    program = Program.build([mod])
    ref = program.resolve(mod, "f")
    from telic.checker import build_theory

    theory, _ = build_theory(program, {})
    g = VCGen(program, ref)
    g.definitional_mode = True
    g.run()
    (ex,) = [e for e in g.exits if e.value is not None]
    enc = Z3Encoder(list(theory.fundefs.values()))
    from telic.vcgen import as_py_number
    value = as_py_number(ex.value)
    is_int = to_python(z3.simplify(enc.term(value.is_int)))
    actual = to_python(z3.simplify(enc.term(value.integer if is_int else value.floating)))
    expected = sum([int(huge), -int(huge), 0.0])
    assert actual == expected == 0.0


def test_python_mixed_sum_keeps_integer_prefix_exact():
    vectors = (
        [9007199254740992, 1, -9007199254740992, 0.0],
        [10**400, -(10**400), 0.0],
        [(1 << 1024) - (1 << 971) + 1, 0.0],
        [1e16, 1, -1e16],
        [1, 0.0, 1e16, 1, -1e16],
        [1, 2, 0.5, 3],
    )
    for xs in vectors:
        literals = ", ".join(repr(x) for x in xs)
        mod = lower_python("sum_mixed.py", f"def f() -> float:\n    return sum([{literals}])\n")
        assert not mod.functions["f"].unsupported, mod.functions["f"].unsupported
        program = Program.build([mod])
        ref = program.resolve(mod, "f")
        g = VCGen(program, ref)
        g.definitional_mode = True
        g.run()
        (ex,) = [e for e in g.exits if e.value is not None]
        from telic.vcgen import as_py_number
        value = as_py_number(ex.value)
        enc = Z3Encoder([])
        is_int = to_python(z3.simplify(enc.term(value.is_int)))
        actual = to_python(z3.simplify(enc.term(value.integer if is_int else value.floating)))
        expected = sum(xs)
        assert actual == expected, (xs, actual, expected)


@pytest.mark.skipif(shutil.which("rustc") is None, reason="rustc not available")
def test_rust_float_to_int_saturates_like_rustc(tmp_path):
    from telic.frontend.rust import lower_rust

    source = """pub fn f(x: f64) -> i32 { x as i32 }
fn main() {
    let xs: [f64; 8] = [f64::NAN, f64::INFINITY, f64::NEG_INFINITY, 1e40, -1e40, 3.9, -3.9, -0.0];
    for x in xs { println!(\"{}\", f(x)); }
}
"""
    path = tmp_path / "cast.rs"
    path.write_text(source)
    binary = tmp_path / "cast"
    subprocess.run(["rustc", "--edition", "2021", str(path), "-o", str(binary)], capture_output=True, text=True, check=True)
    expected = [int(x) for x in subprocess.run([str(binary)], capture_output=True, text=True, check=True).stdout.splitlines()]
    mod = lower_rust(str(path), source, root=str(tmp_path))
    assert not mod.functions["f"].unsupported, mod.functions["f"].unsupported
    inputs = [float("nan"), float("inf"), -float("inf"), 1e40, -1e40, 3.9, -3.9, -0.0]
    for x, want in zip(inputs, expected):
        got = model_value_one(mod, "f", x)
        assert got == want, (x, got, want)


@pytest.mark.skipif(shutil.which("rustc") is None, reason="rustc not available")
def test_rust_float_casts_round_and_widen_like_rustc(tmp_path):
    from telic.frontend.rust import lower_rust

    source = """pub fn narrow(x: f64) -> f32 { x as f32 }
pub fn widen(x: f32) -> f64 { x as f64 }
fn main() {
    let xs: [f64; 6] = [16777217.0, 1e-50, -1e-50, 1e39, -1e39, -0.0];
    for x in xs { println!(\"{:08x}\", narrow(x).to_bits()); }
    let ys: [f32; 6] = [16777217.0, 1e-30, -1e-30, 1e30, -1e30, -0.0];
    for x in ys { println!(\"{:016x}\", widen(x).to_bits()); }
}
"""
    path = tmp_path / "float_cast.rs"
    path.write_text(source)
    binary = tmp_path / "float_cast"
    subprocess.run(["rustc", "--edition", "2021", str(path), "-o", str(binary)], capture_output=True, text=True, check=True)
    bits = subprocess.run([str(binary)], capture_output=True, text=True, check=True).stdout.splitlines()
    mod = lower_rust(str(path), source, root=str(tmp_path))
    xs = [16777217.0, 1e-50, -1e-50, 1e39, -1e39, -0.0]
    ys = [16777217.0, 1e-30, -1e-30, 1e30, -1e30, -0.0]
    for x, want in zip(xs, bits[:6]):
        got = model_value_one(mod, "narrow", x)
        assert struct.pack(">f", got).hex() == want, (x, got, want)
    for x, want in zip(ys, bits[6:]):
        got = model_value_one(mod, "widen", x, L.FLOAT32)
        assert struct.pack(">d", got).hex() == want, (x, got, want)


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
    "len([i for i in range(a, b)])",
    "len([i * 2 for i in range(b)])",
    "len([i + x for i, x in enumerate([a, b, a])])",
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


LIST_IDIOMS = ["([a, b] * 3)[4]", "([7] * a)[a - 1]", "[i * i for i in range(b, 9)][2]", "list(range(a, b + 12))[3]", "(b * [a, 5])[b + 1]", "list(map(lambda x: x * 3 - a, range(b, 9)))[2]", "list(map(lambda x: x // 2, [a, b, 5]))[1]"]


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


@needs_node
def test_javascript_safe_integer_boundary_matches_node(tmp_path):
    from telic.frontend.typescript import lower_typescript_files

    path = tmp_path / "safe_integer.ts"
    path.write_text(
        "export function add(a: number, b: number): number {\n"
        "  //@ requires Number.isSafeInteger(a) && Number.isSafeInteger(b)\n"
        "  return a + b;\n}\n"
    )
    module = lower_typescript_files([str(path)], str(tmp_path))[str(path)]
    limit = 9007199254740991
    pairs = [(limit - 1, 1), (limit, 1), (-limit, -1)]
    js = "const pairs = " + json.dumps(pairs) + "; console.log(JSON.stringify(pairs.map(([a,b]) => a+b)));"
    actual = json.loads(subprocess.run(["node", "-e", js], capture_output=True, text=True, check=True).stdout)
    for (a, b), expected in zip(pairs, actual):
        assert model_value(module, "add", a, b) == expected
