"""The Swift frontend: verdicts pinned in tests/cases/corpus.swift, refutations
confirmed by running the code compiled with swiftc, and telic's model of
Swift's operators compared with the real thing."""

import random
import re
import shutil
import subprocess
from pathlib import Path

import pytest

pytest.importorskip("tree_sitter_swift")

from telic import logic as L  # noqa: E402
from telic.checker import CheckOptions, check  # noqa: E402
from telic.frontend.swift import lower_swift  # noqa: E402
from telic.program import Program  # noqa: E402

CASES = Path(__file__).parent / "cases"
CORPUS = CASES / "corpus.swift"
HAS_SWIFTC = shutil.which("swiftc") is not None
needs_swiftc = pytest.mark.skipif(not HAS_SWIFTC, reason="swiftc not available")


def expectations(path: Path) -> dict[str, str]:
    """'// expect: verdict' above a function, keyed 'Type.name' inside a type."""
    out: dict[str, str] = {}
    owner, depth, pending = None, 0, None
    for line in path.read_text().splitlines():
        m = re.match(r"\s*(?:final\s+)?(?:struct|class|enum|extension)\s+(\w+)", line)
        if m and owner is None:
            owner, depth = m.group(1), 0
        if owner is not None:
            depth += line.count("{") - line.count("}")
        e = re.match(r"\s*// expect: (\w+)", line)
        if e:
            pending = e.group(1)
        else:
            d = re.match(r"\s*(?:(?:mutating|static|public|private)\s+)*(?:func\s+(\w+)|var\s+(\w+)\s*:|(init)\b)", line)
            if d and pending:
                name = d.group(1) or d.group(2) or d.group(3)
                out[f"{owner}.{name}" if owner else name] = pending
                pending = None
        if owner is not None and depth <= 0 and "}" in line:
            owner = None
    return out


@pytest.fixture(scope="module")
def report():
    rep = check([str(CORPUS)], CheckOptions(cache_path=None, lean=False), root=str(CORPUS.parent))
    return rep, {f.fn.name: f for f in rep.functions}


def test_swift_corpus(report):
    rep, got = report
    assert not [p for m in rep.modules for p in m.problems], [p for m in rep.modules for p in m.problems]
    want = expectations(CORPUS)
    assert len(want) > 50
    bad = []
    for name, verdict in want.items():
        f = got.get(name)
        have = f.status if f else "missing"
        if have != verdict:
            detail = [f"{v.ob.id}:{v.status}" for v in f.verdicts if v.status != "proved"] if f else []
            bad.append(f"{name}: expected {verdict}, got {have} {detail} {f.problems if f else ''}")
    assert not bad, "\n".join(bad)


@needs_swiftc
def test_swift_refutations_are_real_failures(report):
    _, got = report
    for name, want in expectations(CORPUS).items():
        if want != "refuted":
            continue
        vs = [v for v in got[name].verdicts if v.status == "refuted"]
        confirmed = [v for v in vs if v.replay is not None and v.replay.confirmed]
        assert confirmed, (name, [(v.ob.id, v.replay.summary if v.replay else None) for v in vs])


@needs_swiftc
def test_corpus_is_valid_swift(tmp_path):
    p = subprocess.run(["swiftc", "-typecheck", str(CORPUS)], capture_output=True, text=True, timeout=600)
    assert p.returncode == 0, p.stderr


# ---------------------------------------------------------------------------
# The model of Swift's operators against swiftc


def swift_int(rnd: random.Random, depth: int = 0) -> str:
    if depth > 2 or rnd.random() < 0.25:
        return rnd.choice(["a", "b", str(rnd.randint(0, 9))])
    x, y, z = (swift_int(rnd, depth + 1) for _ in range(3))
    return rnd.choice(
        [
            f"{x} + {y} * {z}",
            f"{x} * {y} - {z}",
            f"{x} - {y} - {z}",
            f"({x}) / ({y})",
            f"({x}) / (abs({y}) + 1)",
            f"({x}) % ({y} &* 2 &+ 1)",
            f"{x} &+ {y} &* {z}",
            f"-{rnd.choice(['a', 'b'])} * {y}",
            f"-({x}) * {y}",
            f"({swift_bool(rnd, depth + 1)} ? {x} : {y})",
            f"min({x}, {y})",
            f"max({x}, {y})",
            f"abs({x})",
            f"(({swift_bool(rnd, depth + 1)} ? {x} : nil) ?? {y} + 1)",
            f"({swift_bool(rnd, depth + 1)} ? {x} : {swift_bool(rnd, depth + 2)} ? {y} : {z})",
        ]
    )


def swift_bool(rnd: random.Random, depth: int = 0) -> str:
    x, y = swift_int(rnd, depth + 2), swift_int(rnd, depth + 2)
    u, v = swift_int(rnd, depth + 2), swift_int(rnd, depth + 2)
    return rnd.choice(
        [
            f"{x} < {y} && {u} != {v} || {x} == {v}",
            f"{x} >= {y} || {u} < {v} && {x} != {u}",
            f"!({x} < {y}) && {u} <= {v}",
            f"({x}).isMultiple(of: {y})",
            f"{x} + {y} > {u} * {v}",
        ]
    )


def model_value(module, fname, a, b):
    import z3

    from telic.smt import Z3Encoder, to_python
    from telic.vcgen import VCGen

    program = Program.build([module])
    ref = program.resolve(module, fname)
    g = VCGen(program, ref, inputs={"a": L.IntV(a), "b": L.IntV(b)})
    g.definitional_mode = True
    g.run()
    (ex,) = [e for e in g.exits if e.value is not None]
    return to_python(z3.simplify(Z3Encoder([]).term(ex.value)))


@needs_swiftc
def test_swift_integer_semantics_match_swiftc(tmp_path):
    """Random expressions mixing precedence groups, division, remainder,
    wrapping and nil-coalescing: telic's value is swiftc's, or swiftc traps."""
    rnd = random.Random(2026)
    exprs = [swift_int(rnd) for _ in range(60)]
    src = "".join(f"func f{i}(_ a: Int, _ b: Int) -> Int {{\n    return {e}\n}}\n\n" for i, e in enumerate(exprs))
    mod = lower_swift("gen.swift", src)
    for i, e in enumerate(exprs):
        assert not mod.functions[f"f{i}"].unsupported, (e, mod.functions[f"f{i}"].unsupported)
    inputs = [(a, b) for a in (-7, -3, -1, 0, 1, 2, 5, 9) for b in (-4, -2, -1, 1, 3, 7)]
    cases = [(i, a, b) for i in range(len(exprs)) for a, b in rnd.sample(inputs, 6)]
    prog = src + "#if canImport(Glibc)\nimport Glibc\n#else\nimport Darwin\n#endif\nsetvbuf(stdout, nil, _IONBF, 0)\n"
    prog += "let telicFs: [(Int, Int) -> Int] = [" + ", ".join(f"f{i}" for i in range(len(exprs))) + "]\n"
    prog += "let telicCases: [(Int, Int, Int)] = [" + ", ".join(f"({i}, {a}, {b})" for i, a, b in cases) + "]\n"
    prog += "for k in Int(CommandLine.arguments[1])!..<telicCases.count { let (i, a, b) = telicCases[k]; print(\"C \\(k) \\(telicFs[i](a, b))\") }\n"
    (tmp_path / "main.swift").write_text(prog)
    exe = tmp_path / "main"
    c = subprocess.run(["swiftc", "-Onone", "-o", str(exe), str(tmp_path / "main.swift")], capture_output=True, text=True, timeout=900)
    assert c.returncode == 0, c.stderr
    real: dict[int, int | None] = {}
    start = 0
    while start < len(cases):
        r = subprocess.run([str(exe), str(start)], capture_output=True, text=True, timeout=60)
        for line in r.stdout.splitlines():
            _, k, v = line.split()
            real[int(k)] = int(v)
        if r.returncode == 0:
            break
        trapped = max(real, default=start - 1) + 1
        real[trapped] = None  # a trap (division by zero, overflow)
        start = trapped + 1
    checked = 0
    for k, (i, a, b) in enumerate(cases):
        want = real.get(k)
        if want is None:
            continue
        got = model_value(mod, f"f{i}", a, b)
        assert got == want, f"{exprs[i]} at a={a}, b={b}: model {got}, swiftc {want}"
        checked += 1
    assert checked > 250
