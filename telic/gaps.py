"""Spec gaps: attack the contract, not the code.

A proof says the code meets its contract. It says nothing about whether the
contract says enough. ``telic gaps`` makes small, plausible mistakes in a
proved function -- a flipped comparison, an off-by-one, a deleted update --
and re-verifies each mutant against the *unchanged* contract. A mutant that
still verifies, and that provably behaves differently from the original on
some input, is a wrong program the contract accepts. It is reported as a
diff plus that input, which is usually all it takes to see the missing
``@ensures``.
"""

from __future__ import annotations

import copy
import os
import re
import shutil
import tempfile
import time
from dataclasses import dataclass, field
from pathlib import Path

from . import ir
from .checker import CheckOptions, check_modules, load_modules
from .program import FuncRef, Program

MAX_MUTANTS = 40


@dataclass
class Mutant:
    line: int
    before: str
    after: str
    what: str

    def apply(self, source: str) -> str:
        lines = source.split("\n")
        lines[self.line - 1] = self.after
        return "\n".join(lines)


@dataclass
class Gap:
    mutant: Mutant
    args_text: str
    original: str
    mutated: str


@dataclass
class FunctionGaps:
    ref: FuncRef
    total: int = 0
    killed: int = 0
    equivalent: int = 0
    gaps: list[Gap] = field(default_factory=list)
    skipped: str = ""


# ---------------------------------------------------------------------------
# Mutation operators, applied to source text at IR locations


SWAPS = {
    "lt": [("<", "<=")],
    "le": [("<=", "<")],
    "gt": [(">", ">=")],
    "ge": [(">=", ">")],
    "eq": [("===", "!=="), ("==", "!=")],
    "ne": [("!==", "==="), ("!=", "==")],
    "add": [("+", "-")],
    "sub": [("-", "+")],
}


def _code_exprs(fn: ir.Function):
    for s in ir.walk_stmts(fn.body):
        for e in ir.stmt_exprs(s):
            yield from ir.walk_expr(e)


def mutants_for(fn: ir.Function, source: str, language: str) -> list[Mutant]:
    lines = source.split("\n")
    out: list[Mutant] = []
    seen: set[tuple[int, str]] = set()

    def add(line: int, new: str, what: str) -> None:
        old = lines[line - 1]
        if new == old or (line, new) in seen:
            return
        seen.add((line, new))
        out.append(Mutant(line, old, new, what))

    for e in _code_exprs(fn):
        if isinstance(e, ir.Binary) and e.op in SWAPS:
            l, r = e.left.loc, e.right.loc
            if l.line != r.line or l.line == 0 or l.end_col <= 0 or r.col <= l.end_col:
                continue
            text = lines[l.line - 1]
            gap = text[l.end_col:r.col]
            for old, new in SWAPS[e.op]:
                m = re.search(r"(?<![<>=!+\-*/])" + re.escape(old) + r"(?![=<>+\-])", gap)
                if m:
                    mutated = text[: l.end_col + m.start()] + new + text[l.end_col + m.end():]
                    add(l.line, mutated, f"{old} → {new}")
                    break
        elif isinstance(e, ir.Lit) and isinstance(e.value, int) and not isinstance(e.value, bool) and e.loc.line and e.loc.end_col > e.loc.col:
            text = lines[e.loc.line - 1]
            lit = text[e.loc.col:e.loc.end_col]
            if lit.lstrip("-").isdigit():
                v = int(lit)
                for nv in (v + 1, v - 1):
                    add(e.loc.line, text[: e.loc.col] + str(nv) + text[e.loc.end_col:], f"{v} → {nv}")
        elif isinstance(e, ir.Builtin) and e.name in ("min", "max") and e.loc.line:
            text = lines[e.loc.line - 1]
            a, b = ("min", "max") if e.name == "min" else ("max", "min")
            seg = text[e.loc.col:]
            k = seg.find(a + "(")
            if k >= 0:
                add(e.loc.line, text[: e.loc.col + k] + b + text[e.loc.col + k + len(a):], f"{a} → {b}")
    for s in ir.walk_stmts(fn.body):
        ln = s.loc.line
        if not ln or ln > len(lines):
            continue
        text = lines[ln - 1]
        indent = text[: len(text) - len(text.lstrip())]
        if isinstance(s, (ir.Assign, ir.Append, ir.IndexAssign)):
            stripped = text.strip()
            if "+=" in stripped:
                add(ln, text.replace("+=", "-=", 1), "+= → -=")
            elif "-=" in stripped:
                add(ln, text.replace("-=", "+=", 1), "-= → +=")
            one_line = not stripped.endswith(("(", "[", "{", ",", "\\")) and stripped.count("(") == stripped.count(")")
            if one_line and not stripped.startswith(("let ", "const ", "var ")) and "$" not in getattr(s, "name", ""):
                add(ln, indent + ("pass" if language == "python" else ";") + ("" if language == "python" else f" // {stripped}"), "delete statement")
        elif isinstance(s, ir.Return) and s.value is not None:
            m = re.match(r"^(\s*return\s+)(.+?)(;?\s*)$", text)
            if not m:
                continue
            cur = m.group(2).strip()
            ty = s.value.ty
            alts: list[str] = []
            if isinstance(ty, (ir.TInt, ir.TReal)):
                alts.append("0")
            if isinstance(ty, ir.TBool):
                alts += ["True", "False"] if language == "python" else ["true", "false"]
            names = [p.name for p in fn.params] + [n for n in fn.locals if "$" not in n and n not in {p.name for p in fn.params}]
            for n in names:
                if fn.locals.get(n) == ty and n != cur:
                    alts.append(n)
            for alt in alts[:5]:
                add(ln, m.group(1) + alt + m.group(3), f"return {alt}")
        elif isinstance(s, ir.If):
            m = re.match(r"^(\s*)(el)?if (.*):\s*$", text) if language == "python" else re.match(r"^(\s*)(\}?\s*else\s+)?if\s*\((.*)\)(\s*\{?\s*)$", text)
            if m:
                if language == "python":
                    add(ln, f"{m.group(1)}{m.group(2) or ''}if not ({m.group(3)}):", "negate condition")
                else:
                    add(ln, f"{m.group(1)}{m.group(2) or ''}if (!({m.group(3)})){m.group(4)}", "negate condition")
    return out[:MAX_MUTANTS]


# ---------------------------------------------------------------------------


def _lower(path: str, source: str, language: str, root: str) -> ir.Module:
    if language == "python":
        from .frontend.python import lower_python

        return lower_python(os.path.relpath(path, root), source)
    from .frontend.typescript import lower_typescript_files

    return lower_typescript_files([path], root)[path]


def find_gaps(paths: list[str], opts: CheckOptions, root: str, progress=None) -> list[FunctionGaps]:
    from .equiv import check_pair
    from .checker import build_theory

    base_opts = CheckOptions(timeout_ms=opts.timeout_ms, replay=False, lean=False, infer=True, cache_path=opts.cache_path, only=opts.only)
    modules = load_modules(paths, root)
    report = check_modules(modules, base_opts, root=root)
    results: list[FunctionGaps] = []
    tmp = tempfile.mkdtemp(prefix="telic-gaps-")
    try:
        for frep in report.functions:
            fn, mod = frep.fn, frep.ref.module
            if not fn.ensures:
                continue
            fg = FunctionGaps(frep.ref)
            results.append(fg)
            if frep.status != "proved":
                fg.skipped = f"not proved yet ({frep.status}); gaps only make sense for proved functions"
                continue
            muts = mutants_for(fn, mod.source, mod.language)
            fg.total = len(muts)
            for i, mu in enumerate(muts):
                if progress:
                    progress(f"{fn.name}: mutant {i + 1}/{len(muts)}")
                d = os.path.join(tmp, f"m{len(results)}_{i}")
                os.makedirs(d)
                # keep the directory layout so relative imports keep working
                src_path = os.path.join(root, mod.path)
                mpath = os.path.join(d, os.path.basename(mod.path))
                for sib in os.listdir(os.path.dirname(src_path) or "."):
                    full = os.path.join(os.path.dirname(src_path), sib)
                    if os.path.isfile(full) and sib != os.path.basename(mod.path) and sib.endswith((".py", ".ts")):
                        shutil.copy(full, os.path.join(d, sib))
                Path(mpath).write_text(mu.apply(mod.source))
                try:
                    mmod = _lower(mpath, mu.apply(mod.source), mod.language, root)
                except Exception:
                    fg.killed += 1
                    continue
                if mmod.problems or fn.name not in mmod.functions or mmod.functions[fn.name].unsupported:
                    fg.killed += 1
                    continue
                others = [m for m in modules if m.path != mod.path]
                mrep = check_modules(others + [mmod], CheckOptions(timeout_ms=opts.timeout_ms, replay=False, lean=False, cache_path=opts.cache_path, only={fn.name}), root=root)
                mf = next((f for f in mrep.functions if f.ref.module is mmod and f.fn.name == fn.name), None)
                if mf is None or mf.status != "proved":
                    fg.killed += 1
                    continue
                # Survived verification. Is it actually different?
                # a copy: the build qualifies the class names both define, in place
                orig = copy.deepcopy(mod)
                afn, bfn = orig.functions[fn.name], mmod.functions[fn.name]
                program = Program.build(others + [orig, mmod])
                program.root = root  # type: ignore[attr-defined]
                theory, _ = build_theory(program, {})
                a = next(r for r in program.funcs.values() if r.fn is afn)
                b = next(r for r in program.funcs.values() if r.fn is bfn)
                pr = check_pair(program, theory, a, b, root, fn.loc, opts.timeout_ms, n_tests=200)
                if pr.status == "refuted" and pr.witness:
                    w = pr.witness
                    fg.gaps.append(Gap(mu, w["args_text"], w["a_text"].split("→", 1)[1].strip(), w["b_text"].split("→", 1)[1].strip()))
                else:
                    fg.equivalent += 1
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
    return results


# ---------------------------------------------------------------------------


def render_gaps(results: list[FunctionGaps], seconds: float) -> str:
    from .render import Paint, pad

    p = Paint()
    out: list[str] = []
    total = sum(r.total for r in results)
    killed = sum(r.killed for r in results)
    ngaps = sum(len(r.gaps) for r in results)
    out.append(f"{p.bold('telic gaps')}  {p.dim(f'{len(results)} contracted functions · {total} mutants · {seconds:.1f}s')}")
    out.append("")
    for r in results:
        fn = r.ref.fn
        loc = f"{r.ref.module.path}:{fn.loc.line}"
        if r.skipped:
            out.append(f"  {p.gray('·')} {pad(fn.name, 20)}{p.dim(loc)}  {p.dim(r.skipped)}")
            continue
        if not r.gaps:
            out.append(f"  {p.green('✓')} {pad(fn.name, 20)}{p.dim(loc)}  {p.dim(f'every mutant is rejected by the contract ({r.killed} killed, {r.equivalent} equivalent)')}")
            continue
        out.append("")
        head = f"{p.byellow('◌ GAP')} {p.bold(fn.name)} {p.dim('·')} the contract accepts {len(r.gaps)} wrong version{'s' * (len(r.gaps) != 1)}"
        out.append(f"{head}  {p.dim(loc)}")
        for g in r.gaps:
            mu = g.mutant
            w = len(str(mu.line))
            out.append("")
            out.append(p.dim(f"   {' ' * w} │ ") + p.dim(mu.what))
            out.append(p.red(f"   {mu.line:>{w}} - ") + p.red(mu.before.rstrip()))
            out.append(p.green(f"   {mu.line:>{w}} + ") + p.green(mu.after.rstrip()))
            out.append(f"   {p.bold(pad('input', 10))}{g.args_text}")
            out.append(f"   {p.bold(pad('returns', 10))}{g.original} {p.dim('originally,')} {g.mutated} {p.dim('mutated — and both satisfy every @ensures')}")
        out.append("")
        out.append(f"   {p.magenta('hint')}  strengthen the @ensures of {fn.name} until these inputs pin down the result")
        out.append("")
    eq_total = sum(r.equivalent for r in results)
    score = f"{killed}/{total - eq_total}" if total else "0/0"
    tail = [p.bgreen(f"{killed} killed")]
    if ngaps:
        tail.insert(0, p.byellow(f"{ngaps} gap{'s' * (ngaps != 1)}"))
    eq = sum(r.equivalent for r in results)
    if eq:
        tail.append(p.dim(f"{eq} equivalent"))
    out.append("")
    out.append("  ".join(tail) + p.dim(f"   (mutation score {score}; equivalent mutants excluded)"))
    return "\n".join(out)


def cmd_gaps(args) -> int:
    root = os.path.abspath(args.root or os.getcwd())
    opts = args._options(args, root)
    t0 = time.perf_counter()
    results = find_gaps(args.paths, opts, root)
    print(render_gaps(results, time.perf_counter() - t0))
    return 1 if any(r.gaps for r in results) else 0


def add_commands(sub, common, options) -> None:
    g = sub.add_parser("gaps", help="find wrong implementations your contracts still accept")
    common(g)
    g.set_defaults(func=cmd_gaps, _options=options)
