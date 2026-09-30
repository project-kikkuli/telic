"""Spec gaps: attack the contract, not the code.

A proof says the code meets its contract. It says nothing about whether the
contract says enough. ``telic gaps`` makes small, plausible mistakes in a
proved function -- a flipped comparison, an off-by-one, a deleted update --
and re-verifies each mutant against the *unchanged* contract. A mutant that
still verifies, and that provably behaves differently from the original on
some input, is a wrong program the contract accepts. It is reported as a
diff plus that input, which is usually all it takes to see the missing
``@ensures``.

Deterministic operators come first: the small mistakes above, and the
realistic ones by category (a missing None check, a skipped validation or
authorization check, removed error handling, a deleted guard clause), made
by deleting the guard or unwrapping the try. With ``--llm`` a model
(``oracle.py``, task ``mutate``) also writes mutants in those categories.
All go through the same lowering, verification and equivalence check, so a
mutant counts only when the contract accepts it and a witness input shows it
behaves differently. For the gaps that survive, an oracle (task
``strengthen``) proposes a stronger ``@ensures`` or aim; an ``@ensures``
counts only once the original still proves with it and a surviving mutant no
longer does. Proposals are shown, never applied.
"""

from __future__ import annotations

import copy
import difflib
import os
import re
import shutil
import tempfile
import time
from dataclasses import dataclass, field
from pathlib import Path

from . import ir
from . import oracle as oracles
from .checker import CheckOptions, check_modules, load_modules
from .program import FuncRef, Program

MAX_MUTANTS = 40
MAX_PROPOSALS = 6


@dataclass
class Mutant:
    line: int
    before: str
    after: str
    what: str
    end: int = 0  # last line replaced; 0 means just ``line``
    by: str = ""  # the oracle that wrote it; "" for a mutation operator

    def apply(self, source: str) -> str:
        lines = source.split("\n")
        lines[self.line - 1 : self.end or self.line] = self.after.split("\n")
        return "\n".join(lines)

    def diff(self) -> list[tuple[str, int, str]]:
        """('-' or '+', line number, text) for each changed line."""
        a, b = self.before.split("\n"), self.after.split("\n")
        out: list[tuple[str, int, str]] = []
        for tag, i1, i2, j1, j2 in difflib.SequenceMatcher(None, a, b, autojunk=False).get_opcodes():
            if tag != "equal":
                out += [("-", self.line + i, a[i]) for i in range(i1, i2)]
                out += [("+", self.line + j, b[j]) for j in range(j1, j2)]
        return out


@dataclass
class Gap:
    mutant: Mutant
    args_text: str
    original: str
    mutated: str
    closed_by: str = ""  # a verified proposed @ensures that rejects this mutant


@dataclass
class Proposal:
    kind: str  # ensures | aim
    text: str
    by: str
    kills: int = 0  # surviving mutants it rejects, with the original still proved
    note: str = ""  # for an aim: its EARS problems


@dataclass
class FunctionGaps:
    ref: FuncRef
    total: int = 0
    killed: int = 0
    equivalent: int = 0
    gaps: list[Gap] = field(default_factory=list)
    skipped: str = ""
    invalid: int = 0  # oracle mutants that did not parse, lower, or keep the contract
    proposals: list[Proposal] = field(default_factory=list)
    rejected: int = 0  # proposed @ensures the original does not prove, or that reject nothing
    notes: list[str] = field(default_factory=list)


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
    out = out[:MAX_MUTANTS]
    text = function_text(source, fn)
    done = {text.strip()} | {m.apply(source) for m in out}
    for key, rule in _RULES.items():
        got = rule(text, language)
        if got and got.strip() not in done:
            done.add(got.strip())
            out.append(Mutant(fn.loc.line, text, got, key.replace("_", " "), end=max(fn.end_line, fn.loc.line)))
    return out


# ---------------------------------------------------------------------------
# Mutants an oracle writes: realistic bugs by category


CATEGORIES = {
    "null_check": "missing None check: remove a None/null/undefined check, so a missing value flows on",
    "validation": "skipped validation: remove or bypass an input validation that raises or rejects",
    "auth": "skipped authorization: remove or bypass a permission, ownership or role check",
    "error_handling": "removed error handling: drop a try/except (try/catch) so the error escapes",
    "guard_clause": "deleted guard clause: remove an early return that handles a special case",
}


def _marker(language: str) -> str:
    return "#@" if language == "python" else "//@"


def function_text(source: str, fn: ir.Function) -> str:
    return "\n".join(source.split("\n")[fn.loc.line - 1 : max(fn.end_line, fn.loc.line)])


def _contract_lines(text: str, language: str) -> list[str]:
    return [" ".join(x.split()) for x in text.split("\n") if x.strip().startswith(_marker(language))]


def _clauses(fn: ir.Function) -> list[str]:
    return [f"{c.kind} {c.text}" for c in fn.requires + fn.ensures + fn.raises]


def _aims(fn: ir.Function, modules: list[ir.Module]) -> list[dict[str, str]]:
    from .aim import split_by

    decls = {d.id: split_by(d.text)[0] for m in modules for d in m.aims}
    return [{"id": i, "text": decls.get(i, "")} for i in fn.aims]


def mutate_request(fn: ir.Function, mod: ir.Module, aims: list[dict[str, str]]) -> tuple[dict, dict]:
    """The typed request for realistic mutants, one text question per
    category (the prompt shape of hyeus's mutate.txt)."""
    state = {
        "function": function_text(mod.source, fn),
        "language": mod.language,
        "file": mod.path,
        "name": fn.name,
        "lines": [fn.loc.line, fn.end_line],
        "contract": _clauses(fn),
        "aims": aims,
        "note": f"The '{_marker(mod.language)}' comments are the contract a verifier proved the function against. "
        "A mutant is a wrong version of the function; the verifier will check it against the unchanged contract.",
    }
    questions = {
        key: {
            "type": "text",
            "category": key,
            "instructions": f"Write ONE realistic bug of this kind into the function: {desc}. Answer with the complete "
            "mutated function, syntactically valid, with the original indentation, name, signature and every "
            f"'{_marker(mod.language)}' comment unchanged. Make the mutation subtle, the kind that ships to production. "
            "If the function has nothing of this kind, answer null.",
        }
        for key, desc in CATEGORIES.items()
    }
    return state, questions


def oracle_mutants(fn: ir.Function, mod: ir.Module, modules: list[ir.Module], spec: str | None, root: str) -> tuple[list[Mutant], int, list[str]]:
    """(mutants, answers that were not a usable mutant, oracle notes)."""
    state, questions = mutate_request(fn, mod, _aims(fn, modules))
    got = oracles.consult("mutate", state, questions, spec=spec, root=root)
    orig = state["function"]
    name = fn.name.rsplit(".", 1)[-1]
    out: list[Mutant] = []
    bad = 0
    seen = {orig.strip()}
    for key in questions:
        a = got.answers.get(key)
        text = _unfence(a.get("text") or "") if a else ""
        if not text.strip():
            continue
        if text.strip() in seen:
            continue
        seen.add(text.strip())
        if name not in text or _contract_lines(text, mod.language) != _contract_lines(orig, mod.language):
            bad += 1  # renamed the function or touched the contract: not a mutant of this function
            continue
        out.append(Mutant(fn.loc.line, orig, text.rstrip("\n"), key.replace("_", " "), end=max(fn.end_line, fn.loc.line), by=a.get("by", got.oracle)))
    return out, bad, got.notes


def _unfence(text: str) -> str:
    lines = text.strip("\n").split("\n")
    if lines and lines[0].lstrip().startswith("```"):
        lines = lines[1:]
        if lines and lines[-1].strip().startswith("```"):
            lines = lines[:-1]
    return "\n".join(lines)


# The same categories as deterministic operators: delete the first matching
# guard, or unwrap the first try. They run on every function; a model's
# mutants are an opt-in supplement.

_NONE = re.compile(r"\bNone\b|\bnull\b|\bundefined\b")
_AUTH = re.compile(r"auth|admin|owner|permi|role|allowed|grant|token|session|logged|can_|may_|is_staff|superuser", re.I)


def _indent(s: str) -> int:
    return len(s) - len(s.lstrip())


def _guards(lines: list[str], language: str):
    """(first, past-last, condition, body) of each ``if`` with no else whose
    only statement returns, raises or throws."""
    for i, line in enumerate(lines):
        if language == "python":
            m = re.match(r"^(\s*)if (.+?):\s*(\S.*)?$", line)
            if not m:
                continue
            ind = len(m.group(1))
            if m.group(3):
                body, k = m.group(3), i + 1
            else:
                j = next((j for j in range(i + 1, len(lines)) if lines[j].strip()), None)
                if j is None or _indent(lines[j]) <= ind:
                    continue
                body = lines[j].strip()
                k = next((k for k in range(j + 1, len(lines)) if lines[k].strip()), len(lines))
                if k < len(lines) and _indent(lines[k]) > ind:
                    continue  # more than one statement
                k = j + 1
            nxt = next((x for x in lines[k:] if x.strip()), "")
            if re.match(r"^\s*(elif|else)\b", nxt) and _indent(nxt) == ind:
                continue
            if re.match(r"^(return|raise)\b", body):
                yield i, k, m.group(2), body
        else:
            m = re.match(r"^(\s*)if\s*\((.*)\)\s*(.*?)\s*$", line)
            if not m:
                continue
            rest = m.group(3)
            if rest == "{":
                j = i + 1
                if j + 1 >= len(lines) or lines[j + 1].strip() != "}":
                    continue
                body, k = lines[j].strip(), j + 2
            elif rest:
                body, k = rest.strip("{} "), i + 1
            else:
                continue
            nxt = next((x for x in lines[k:] if x.strip()), "")
            if re.match(r"^\s*(\}\s*)?else\b", nxt):
                continue
            if re.match(r"^(return|throw)\b", body):
                yield i, k, m.group(2), body


def _drop_guard(text: str, language: str, want) -> str | None:
    lines = text.split("\n")
    for i, k, cond, body in _guards(lines, language):
        if want(cond, body):
            return "\n".join(lines[:i] + lines[k:])
    return None


def _drop_try(text: str, language: str) -> str | None:
    lines = text.split("\n")
    for i, line in enumerate(lines):
        ind = _indent(line)
        if language == "python" and line.strip() == "try:":
            j = next((j for j in range(i + 1, len(lines)) if lines[j].strip() and _indent(lines[j]) <= ind), None)
            if j is None or not lines[j].strip().startswith("except"):
                continue
            k = j
            while k < len(lines) and (not lines[k].strip() or _indent(lines[k]) > ind or (_indent(lines[k]) == ind and lines[k].strip().startswith("except"))):
                k += 1
            if k < len(lines) and re.match(r"^(else|finally)\b", lines[k].strip()):
                continue
            body = lines[i + 1 : j]
            step = min((_indent(x) for x in body if x.strip()), default=ind) - ind
            return "\n".join(lines[:i] + [x[step:] if x.strip() else x for x in body] + lines[k:])
        if language != "python" and re.match(r"^\s*try\s*\{\s*$", line):
            j = next((j for j in range(i + 1, len(lines)) if re.match(r"^\s*\}\s*catch\b.*\{\s*$", lines[j]) and _indent(lines[j]) == ind), None)
            if j is None:
                continue
            k = next((k for k in range(j + 1, len(lines)) if lines[k].strip() == "}" and _indent(lines[k]) == ind), None)
            if k is None or re.match(r"^\s*finally\b", next((x for x in lines[k + 1 :] if x.strip()), "")):
                continue
            body = lines[i + 1 : j]
            step = min((_indent(x) for x in body if x.strip()), default=ind) - ind
            return "\n".join(lines[:i] + [x[step:] if x.strip() else x for x in body] + lines[k + 1 :])
    return None


_RULES = {
    "null_check": lambda t, lang: _drop_guard(t, lang, lambda c, b: bool(_NONE.search(c))),
    "validation": lambda t, lang: _drop_guard(t, lang, lambda c, b: b.startswith(("raise", "throw")) and not _AUTH.search(c)),
    "auth": lambda t, lang: _drop_guard(t, lang, lambda c, b: bool(_AUTH.search(c))),
    "error_handling": _drop_try,
    "guard_clause": lambda t, lang: _drop_guard(t, lang, lambda c, b: b.startswith("return") and not _NONE.search(c)),
}


# ---------------------------------------------------------------------------
# Proposals: a stronger @ensures, verified against the original and the mutants


def strengthen_request(fn: ir.Function, mod: ir.Module, gaps: list[Gap], aims: list[dict[str, str]], candidates: list[str]) -> tuple[dict, dict]:
    state = {
        "function": function_text(mod.source, fn),
        "language": mod.language,
        "contract": _clauses(fn),
        "aims": aims,
        "wrong_versions": [
            {"function": _mutant_text(mod.source, fn, g.mutant), "input": g.args_text, "original_returns": g.original, "wrong_returns": g.mutated}
            for g in gaps
        ],
        "candidates": candidates,
        "note": "Every wrong version satisfies the whole contract, yet on the input shown it returns something else. "
        "The contract is too weak. Contract clauses use the language's expression syntax plus result, old(e) and implies(a, b).",
    }
    questions = {
        "ensures": {
            "type": "text",
            "instructions": "Propose postconditions the original function satisfies on every input its preconditions allow, "
            "and that the wrong versions violate. One clause per line, strongest first, just the expression (no "
            f"'{_marker(mod.language)} ensures' prefix).",
        }
    }
    if aims:
        questions["aim"] = {
            "type": "text",
            "instructions": "Rewrite the aim sentence (one EARS sentence, one 'shall') so that it also rules out the wrong "
            "versions' behaviour. Answer with the sentence only.",
        }
    return state, questions


@oracles.builtin("strengthen")
def _builtin_strengthen(state, questions):
    """The template facts telic propose tries, for verification to sort out.
    No aim rewrite: that needs a reader."""
    have = {" ".join(c.split()) for c in state.get("contract", [])}
    cands = [c for c in state.get("candidates", []) if f"ensures {' '.join(c.split())}" not in have]
    if "ensures" in questions and cands:
        return {"ensures": {"type": "text", "text": "\n".join(cands)}}
    return {}


def _mutant_text(source: str, fn: ir.Function, mu: Mutant) -> str:
    grow = len(mu.after.split("\n")) - ((mu.end or mu.line) - mu.line + 1)
    return "\n".join(mu.apply(source).split("\n")[fn.loc.line - 1 : max(fn.end_line, fn.loc.line) + grow])


def _proposed_clauses(text: str, fn: ir.Function) -> list[str]:
    have = {" ".join(c.text.split()) for c in fn.ensures}
    out: list[str] = []
    for line in _unfence(text).split("\n"):
        c = re.sub(r"^\s*(?:[-*]\s+|\d+[.)]\s+)?(?:#@|//@)?\s*", "", line).strip().rstrip(";")
        if re.match(r"^(requires|raises|invariant|assume)\b", c):
            continue
        c = " ".join(re.sub(r"^ensures\s+", "", c).split())
        if c and c not in have and c not in out:
            out.append(c)
    return out[:MAX_PROPOSALS]


def _stage(tmp: str, tag: str, root: str, mod: ir.Module, source: str) -> str:
    """Write ``source`` as the module into a fresh directory next to copies
    of its siblings, so relative imports keep working."""
    d = tempfile.mkdtemp(prefix=tag, dir=tmp)
    src_path = os.path.join(root, mod.path)
    for sib in os.listdir(os.path.dirname(src_path) or "."):
        full = os.path.join(os.path.dirname(src_path), sib)
        if os.path.isfile(full) and sib != os.path.basename(mod.path) and sib.endswith((".py", ".ts")):
            shutil.copy(full, os.path.join(d, sib))
    path = os.path.join(d, os.path.basename(mod.path))
    Path(path).write_text(source)
    return path


def clause_statuses(tmp: str, tag: str, root: str, mod: ir.Module, source: str, fn_name: str, clauses: list[str], others: list[ir.Module], opts: CheckOptions) -> dict[str, str]:
    """Insert ``clauses`` as @ensures into the function in ``source``, check
    it, and return each clause's status (empty if it could not be checked)."""
    from .propose import insertion_point

    path = _stage(tmp, tag, root, mod, source)
    try:
        fn = _lower(path, source, mod.language, root).functions.get(fn_name)
        pt = insertion_point(source, fn, mod.language) if fn else None
        if pt is None:
            return {}
        lines = source.split("\n")
        lines[pt[0] : pt[0]] = [f"{pt[1]}{_marker(mod.language)} ensures {c}" for c in clauses]
        text = "\n".join(lines)
        Path(path).write_text(text)
        m = _lower(path, text, mod.language, root)
    except Exception:  # noqa: BLE001 - a clause that does not parse is not a proposal
        return {}
    if m.problems or fn_name not in m.functions or m.functions[fn_name].unsupported:
        return {}
    rep = check_modules(others + [m], CheckOptions(timeout_ms=opts.timeout_ms, replay=False, lean=False, cache_path=opts.cache_path, only={fn_name}), root=root)
    f = next((f for f in rep.functions if f.ref.module is m and f.fn.name == fn_name), None)
    if f is None or f.status in ("unsupported", "error"):
        return {}
    st: dict[str, str] = {}
    for v in f.verdicts:
        if v.ob.clause is not None and v.ob.clause.text in clauses:
            prev = st.get(v.ob.clause.text)
            st[v.ob.clause.text] = v.status if prev in (None, "proved") else prev
    return st


def propose_fixes(fg: FunctionGaps, fn: ir.Function, mod: ir.Module, modules: list[ir.Module], program: Program, spec: str | None, root: str, opts: CheckOptions, tmp: str) -> None:
    from .aim import ears_problems
    from .propose import ensures_candidates

    others = [m for m in modules if m.path != mod.path]
    aims = _aims(fn, modules)
    cands = ensures_candidates(fn, program, mod.language) if mod.language in ("python", "typescript", "rust") else []
    state, questions = strengthen_request(fn, mod, fg.gaps, aims, cands)
    got = oracles.consult("strengthen", state, questions, spec=spec, root=root)
    fg.notes += got.notes
    ans = got.answers.get("ensures")
    clauses = _proposed_clauses(ans.get("text") or "", fn) if ans else []
    if clauses:
        on_original = clause_statuses(tmp, "orig", root, mod, mod.source, fn.name, clauses, others, opts)
        proved = [c for c in clauses if on_original.get(c) == "proved"]
        kills = {c: 0 for c in proved}
        for i, g in enumerate(fg.gaps if proved else []):
            st = clause_statuses(tmp, f"fix{i}", root, mod, g.mutant.apply(mod.source), fn.name, proved, others, opts)
            for c in proved:
                if c in st and st[c] != "proved":
                    kills[c] += 1
                    g.closed_by = g.closed_by or c
        for c in proved:
            if kills[c]:
                fg.proposals.append(Proposal("ensures", c, ans.get("by", got.oracle), kills[c]))
        fg.rejected += len(clauses) - sum(1 for c in proved if kills[c])
        fg.proposals.sort(key=lambda x: -x.kills)
    a = got.answers.get("aim")
    if a and (a.get("text") or "").strip():
        text = " ".join(_unfence(a["text"]).split())
        fg.proposals.append(Proposal("aim", text, a.get("by", got.oracle), note="; ".join(ears_problems(text))))


# ---------------------------------------------------------------------------


def _lower(path: str, source: str, language: str, root: str) -> ir.Module:
    if language == "python":
        from .frontend.python import lower_python

        return lower_python(os.path.relpath(path, root), source)
    from .frontend.typescript import lower_typescript_files

    return lower_typescript_files([path], root)[path]


def attempt(tmp: str, tag: str, mu: Mutant, fn: ir.Function, mod: ir.Module, others: list[ir.Module], root: str, opts: CheckOptions) -> tuple[str, ir.Module | None]:
    """Verify a mutant against the unchanged contract: ("invalid" | "killed" |
    "survived", its lowered module)."""
    src = mu.apply(mod.source)
    mpath = _stage(tmp, tag, root, mod, src)
    try:
        mmod = _lower(mpath, src, mod.language, root)
    except Exception:  # noqa: BLE001 - a mutant the frontend rejects is not a program
        return "invalid", None
    if mmod.problems or fn.name not in mmod.functions or mmod.functions[fn.name].unsupported:
        return "invalid", mmod
    mrep = check_modules(others + [mmod], CheckOptions(timeout_ms=opts.timeout_ms, replay=False, lean=False, cache_path=opts.cache_path, only={fn.name}), root=root)
    mf = next((f for f in mrep.functions if f.ref.module is mmod and f.fn.name == fn.name), None)
    return ("survived" if mf is not None and mf.status == "proved" else "killed"), mmod


# ---------------------------------------------------------------------------
# Trivial implementations: what a safety aim's lemmas must rule out


def trivial_mutants(fn: ir.Function, mod: ir.Module) -> list[Mutant]:
    """The function with an immediate return of a default value, or an
    immediate raise, before its first statement."""
    from .propose import insertion_point

    if mod.language not in ("python", "typescript"):
        return []
    lines = mod.source.split("\n")
    pt = insertion_point(mod.source, fn, mod.language)
    if pt is None:
        return []
    at, indent = pt
    doc = re.compile(r"^\s*[rRbBuU]?(\"\"\"|\'\'\'|\"|\')")
    if mod.language == "python" and doc.match(lines[at]):
        q = doc.match(lines[at]).group(1)
        rest = lines[at].strip().lstrip("rRbBuU")[len(q):]
        while q not in rest and at + 1 < len(lines):
            at += 1
            rest = lines[at]
        at += 1
    while at < len(lines) and (not lines[at].strip() or lines[at].strip().startswith(_marker(mod.language))):
        at += 1
    py = mod.language == "python"
    ret = fn.ret
    value = (
        "0" if isinstance(ret, (ir.TInt, ir.TReal))
        else ("False" if py else "false") if isinstance(ret, ir.TBool)
        else '""' if isinstance(ret, ir.TStr)
        else "[]" if isinstance(ret, ir.TList)
        else ("None" if py else "undefined") if isinstance(ret, ir.TOption)
        else "" if isinstance(ret, ir.TNone)
        else None
    )
    bodies = []
    if value is not None:
        bodies.append(f"return {value}".rstrip() + ("" if py else ";"))
    bodies.append('raise RuntimeError("stub")' if py else 'throw new Error("stub");')
    out = []
    for b in bodies:
        before = lines[at] if at < len(lines) else ""
        out.append(Mutant(at + 1, before, f"{indent}{b}\n{before}", b.rstrip(";")))
    return out


def trivially_met(fn: ir.Function, mod: ir.Module, modules: list[ir.Module], root: str, opts: CheckOptions) -> str | None:
    """The first trivial implementation that still meets the function's
    whole contract, or None."""
    others = [m for m in modules if m.path != mod.path]
    tmp = tempfile.mkdtemp(prefix="telic-trivial-")
    try:
        for i, mu in enumerate(trivial_mutants(fn, mod)):
            if attempt(tmp, f"t{i}", mu, fn, mod, others, root, opts)[0] == "survived":
                return mu.what
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
    return None


def find_gaps(paths: list[str], opts: CheckOptions, root: str, progress=None, oracle: str | None = None, llm: bool = False, propose: bool = True) -> list[FunctionGaps]:
    """``llm``: also ask the oracle (a model) for realistic mutants and for
    the stronger contract; without it, proposals come from the builtin
    templates and nothing leaves the machine."""
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
            if mod.language not in ("python", "typescript"):
                fg.skipped = f"gaps run on Python and TypeScript; {mod.language} mutants cannot be replayed yet"
                continue
            muts = mutants_for(fn, mod.source, mod.language)
            if llm:
                if progress:
                    progress(f"{fn.name}: asking for realistic mutants")
                more, fg.invalid, notes = oracle_mutants(fn, mod, modules, oracle, root)
                fg.notes += notes
                muts += more
            fg.total = len(muts)
            others = [m for m in modules if m.path != mod.path]
            for i, mu in enumerate(muts):
                if progress:
                    progress(f"{fn.name}: mutant {i + 1}/{len(muts)}")
                verdict, mmod = attempt(tmp, f"m{len(results)}_{i}", mu, fn, mod, others, root, opts)
                if verdict == "invalid" and mu.by:
                    fg.invalid += 1  # a model's mutant outside the supported subset says nothing about the contract
                    fg.total -= 1
                    continue
                if verdict != "survived":
                    fg.killed += 1
                    continue
                assert mmod is not None
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
            if propose and fg.gaps:
                if progress:
                    progress(f"{fn.name}: proposing a stronger contract")
                propose_fixes(fg, fn, mod, modules, report.program, oracle if llm else "builtin", root, opts, tmp)
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
            out += [f"    {p.dim('note  ' + n)}" for n in r.notes]
            continue
        out.append("")
        head = f"{p.byellow('◌ GAP')} {p.bold(fn.name)} {p.dim('·')} the contract accepts {len(r.gaps)} wrong version{'s' * (len(r.gaps) != 1)}"
        out.append(f"{head}  {p.dim(loc)}")
        for g in r.gaps:
            mu = g.mutant
            diff = mu.diff()
            w = max((len(str(n)) for _, n, _ in diff), default=1)
            out.append("")
            out.append(p.dim(f"   {' ' * w} │ ") + p.dim(mu.what + (f" · written by {mu.by}" if mu.by else "")))
            for sign, n, text in diff:
                paint = p.red if sign == "-" else p.green
                out.append(paint(f"   {n:>{w}} {sign} ") + paint(text.rstrip()))
            out.append(f"   {p.bold(pad('input', 10))}{g.args_text}")
            out.append(f"   {p.bold(pad('returns', 10))}{g.original} {p.dim('originally,')} {g.mutated} {p.dim('mutated — and both satisfy every @ensures')}")
        out.append("")
        marker = "#@" if r.ref.module.language == "python" else "//@"
        fixes = [x for x in r.proposals if x.kind == "ensures"]
        for x in fixes:
            out.append(f"   {p.magenta('propose')}  {marker} ensures {x.text}")
            out.append(p.dim(f"            the original still proves; rejects {x.kills} of {len(r.gaps)} wrong version{'s' * (len(r.gaps) != 1)} · {x.by} · not applied"))
        for x in r.proposals:
            if x.kind == "aim":
                out.append(f"   {p.magenta('propose')}  aim {', '.join(fn.aims)}: {x.text}")
                out.append(p.dim(f"            a sentence, not checked{' (' + x.note + ')' if x.note else ''} · {x.by} · not applied"))
        if not fixes:
            out.append(f"   {p.magenta('hint')}  strengthen the @ensures of {fn.name} until these inputs pin down the result")
        if r.rejected and fixes:
            out.append(p.dim(f"            {r.rejected} other proposal{'s' * (r.rejected != 1)} did not verify"))
        out += [f"   {p.dim('note  ' + n)}" for n in r.notes]
        out.append("")
    eq_total = sum(r.equivalent for r in results)
    score = f"{killed}/{total - eq_total}" if total else "0/0"
    tail = [p.bgreen(f"{killed} killed")]
    if ngaps:
        tail.insert(0, p.byellow(f"{ngaps} gap{'s' * (ngaps != 1)}"))
    if eq_total:
        tail.append(p.dim(f"{eq_total} equivalent"))
    invalid = sum(r.invalid for r in results)
    if invalid:
        tail.append(p.dim(f"{invalid} unusable model mutant{'s' * (invalid != 1)}"))
    out.append("")
    out.append("  ".join(tail) + p.dim(f"   (mutation score {score}; equivalent mutants excluded)"))
    return "\n".join(out)


def cmd_gaps(args) -> int:
    root = os.path.abspath(args.root or os.getcwd())
    opts = args._options(args, root)
    t0 = time.perf_counter()
    results = find_gaps(args.paths, opts, root, oracle=args.oracle, llm=args.llm or args.oracle is not None, propose=not args.no_propose)
    print(render_gaps(results, time.perf_counter() - t0))
    return 1 if any(r.gaps for r in results) else 0


def add_commands(sub, common, options) -> None:
    g = sub.add_parser("gaps", help="find wrong implementations your contracts still accept")
    common(g)
    g.add_argument("--llm", action="store_true", help="also have a model write realistic mutants and propose contracts (claude -p if installed; see telic oracle)")
    g.add_argument("--oracle", default=None, help="the oracle for --llm (implies it)")
    g.add_argument("--no-propose", action="store_true", help="do not ask for a stronger contract where gaps survive")
    g.set_defaults(func=cmd_gaps, _options=options)
