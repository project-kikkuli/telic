"""Proposing contracts and aims for code that has none.

Three things, in increasing order of judgment:

1. **Facts about the code as it is.** telic writes candidate postconditions
   into a scratch copy of the project, checks them, and keeps the ones that
   are proved (Houdini: drop what fails, re-check, until nothing changes).
   A fact says what the code *does*. Whether that is what it *should* do is
   the reader's call: a fact can faithfully describe a bug.
2. **Preconditions that make a function crash-free.** For each function that
   can crash (division by zero, an index, a missing key, None, overflow),
   candidate ``requires`` are tried one at a time; the ones that remove every
   crash are reported. Adopting one moves the obligation to the callers.
3. **Draft aims** (``--aims``). Each proved fact is rendered as an
   EARS sentence, and an oracle (a classifier such as Jev, the builtin
   rules, or an LLM; see ``oracle.py``) sorts them into requirements,
   details and likely bugs. A generative oracle may also rephrase them and
   name requirements nothing proves yet. A requirement is the reader's
   decision.

Nothing is written to the source unless ``--write`` is given, and then only
the facts and preconditions (never a model's aim draft).
"""

from __future__ import annotations

import ast
import json
import os
import re
import shutil
import tempfile
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

from . import ir

CRASH_KINDS = {"div", "index", "none", "key", "overflow"}
MAX_ROUNDS = 5


@dataclass
class Proposal:
    module: str  # path relative to root
    func: str
    language: str
    line: int  # the function's line
    end_line: int = 0
    facts: list[str] = field(default_factory=list)  # proved clause payloads ('ensures ...')
    fixes: list[tuple[str, list[str]]] = field(default_factory=list)  # (requires payload, crashes it removes)
    crashes: list[str] = field(default_factory=list)  # what can crash now
    skipped: str = ""


# ---------------------------------------------------------------------------
# Candidate clauses, in each language's syntax


class Syntax:
    #@ invariant self.lang == "python" or self.lang == "typescript" or self.lang == "rust"

    def __init__(self, lang: str):
        #@ requires lang == "python" or lang == "typescript" or lang == "rust"
        self.lang = lang
        self.marker = "#@" if lang == "python" else "//@"

    def len(self, x: str) -> str:
        return {"python": f"len({x})", "typescript": f"{x}.length", "rust": f"{x}.len()"}[self.lang]

    def eq(self, a: str, b: str) -> str:
        return f"{a} === {b}" if self.lang == "typescript" else f"{a} == {b}"

    def present(self, x: str) -> str:
        return {"python": f"{x} is not None", "typescript": f"{x} !== undefined", "rust": f"{x}.is_some()"}[self.lang]

    def all_nonneg(self, xs: str) -> str:
        return {"python": f"all(e >= 0 for e in {xs})", "typescript": f"{xs}.every(e => e >= 0)", "rust": f"{xs}.iter().all(|e| e >= 0)"}[self.lang]

    def all_in(self, xs: str, ys: str) -> str:
        return {"python": f"all(e in {ys} for e in {xs})", "typescript": f"{xs}.every(e => {ys}.includes(e))", "rust": f"{xs}.iter().all(|e| {ys}.contains(e))"}[self.lang]

    def self_name(self) -> str:
        return "this" if self.lang == "typescript" else "self"

    def key_in(self, k: str, d: str) -> str:
        return {"python": f"{k} in {d}", "typescript": f"{d}.has({k})", "rust": f"{d}.contains_key(&{k})"}[self.lang]


def ensures_candidates(fn: ir.Function, program: Any, lang: str) -> list[str]:
    #@ requires lang == "python" or lang == "typescript" or lang == "rust"
    s = Syntax(lang)
    out: list[str] = []
    ret = fn.ret
    params = [p for p in fn.params if p.name != "self"]
    nums = [p.name for p in params if isinstance(p.ty, (ir.TInt, ir.TReal))]
    lists = [p.name for p in params if isinstance(p.ty, ir.TList)]
    if isinstance(ret, (ir.TInt, ir.TReal)):
        out += ["result >= 0", "result > 0"]
        for p in nums:
            out += [f"result <= {p}", f"result >= {p}", s.eq("result", p)]
        for xs in lists:
            out += [f"result <= {s.len(xs)}", f"result < {s.len(xs)}"]
    elif isinstance(ret, ir.TList):
        for xs in lists:
            if params and next(p for p in params if p.name == xs).ty == ret:
                out += [s.eq(s.len("result"), s.len(xs)), f"{s.len('result')} <= {s.len(xs)}", s.all_in("result", xs)]
        if isinstance(ret.elem, (ir.TInt, ir.TReal)):
            out.append(s.all_nonneg("result"))
        for p in nums:
            if isinstance(next(q for q in params if q.name == p).ty, ir.TInt):
                out.append(s.eq(s.len("result"), p))
    elif isinstance(ret, ir.TOption) and not isinstance(ret.inner, (ir.TList, ir.TDict)):
        out.append(s.present("result"))
    elif isinstance(ret, ir.TStr):
        pass
    # methods: what happens to the object's own numeric fields
    self_p = next((p for p in fn.params if p.name == "self"), None)
    if self_p is not None and isinstance(self_p.ty, ir.TClass) and not fn.name.endswith(("__init__", ".constructor", ".new")):
        decl = program.classes.get(self_p.ty.name)
        me = s.self_name()
        for fname, fty in decl.fields if decl else []:
            if isinstance(fty, (ir.TInt, ir.TReal)):
                f = f"{me}.{fname}"
                out += [s.eq(f, f"old({f})"), f"{f} >= old({f})", f"{f} <= old({f})", f"{f} >= 0"]
            elif isinstance(fty, (ir.TStr, ir.TBool)):
                f = f"{me}.{fname}"
                out.append(s.eq(f, f"old({f})"))
            elif isinstance(fty, ir.TList):
                f = f"{me}.{fname}"
                out += [s.eq(s.len(f), f"old({s.len(f)})"), f"{s.len(f)} >= old({s.len(f)})"]
    if lang == "rust":
        # an unsigned result is non-negative by its type: not worth saying
        out = [c for c in out if c not in ("result >= 0",)]
    return out


def requires_candidates(fn: ir.Function, lang: str) -> list[str]:
    #@ requires lang == "python" or lang == "typescript" or lang == "rust"
    s = Syntax(lang)
    out: list[str] = []
    params = [p for p in fn.params if p.name != "self"]
    for p in params:
        if isinstance(p.ty, ir.TList):
            out.append(f"{s.len(p.name)} > 0")
        elif isinstance(p.ty, (ir.TInt, ir.TReal)):
            out += [f"{p.name} != 0" if lang != "typescript" else f"{p.name} !== 0", f"{p.name} > 0", f"{p.name} >= 0"]
        elif isinstance(p.ty, ir.TOption):
            out.append(s.present(p.name))
    for d in params:
        if isinstance(d.ty, ir.TDict):
            for k in params:
                if k.ty == d.ty.key:
                    out.append(s.key_in(k.name, d.name))
    lists = [p for p in params if isinstance(p.ty, ir.TList)]
    for xs in lists:
        for i in params:
            if isinstance(i.ty, ir.TInt):
                out.append(f"{i.name} < {s.len(xs.name)}" if lang != "python" else f"0 <= {i.name} < {s.len(xs.name)}")
    return out


# ---------------------------------------------------------------------------
# Writing clauses into a scratch copy


def insertion_point(source: str, fn: ir.Function, lang: str) -> tuple[int, str] | None:
    """(0-based line index to insert before, indentation) for the first lines
    of a function's body, or None if it has no multi-line body."""
    lines = source.splitlines()
    if lang == "python":
        try:
            tree = ast.parse(source)
        except SyntaxError:
            return None
        target = fn.loc.line
        for node in ast.walk(tree):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) and node.lineno == target:
                first = node.body[0]
                if first.lineno == node.lineno:
                    return None
                ln = first.lineno - 1
                indent = lines[ln][: len(lines[ln]) - len(lines[ln].lstrip())]
                return ln, indent
        return None
    # brace languages: the first '{' at depth 0 after the parameter list
    i = fn.loc.line - 1
    depth = 0
    seen_paren = False
    for j in range(i, min(len(lines), i + 40)):
        line = re.sub(r"//.*$", "", lines[j])
        for ch in line:
            if ch in "([":
                depth += 1
                seen_paren = True
            elif ch in ")]":
                depth -= 1
            elif ch == "{" and depth == 0 and seen_paren:
                if line.rstrip().endswith("{") and j + 1 < len(lines):
                    nxt = next((k for k in range(j + 1, len(lines)) if lines[k].strip()), None)
                    if nxt is None or lines[nxt].strip().startswith("}"):
                        return None
                    indent = lines[nxt][: len(lines[nxt]) - len(lines[nxt].lstrip())]
                    return j + 1, indent
                return None
    return None


def write_scratch(root: str, modules: list[ir.Module], clauses: dict[tuple[str, str], list[str]], work: str) -> dict[tuple[str, str], int]:
    """Copy the project's modules into ``work`` with clauses inserted.
    Returns where each function's clauses begin (for matching verdicts)."""
    starts: dict[tuple[str, str], int] = {}
    for m in modules:
        src = Path(root, m.path).read_text() if not os.path.isabs(m.path) else Path(m.path).read_text()
        lines = src.splitlines()
        inserts: list[tuple[int, list[str], tuple[str, str]]] = []
        for fn in m.functions.values():
            cs = clauses.get((m.path, fn.name))
            if not cs:
                continue
            pt = insertion_point(src, fn, m.language)
            if pt is None:
                continue
            ln, indent = pt
            marker = "#@" if m.language == "python" else "//@"
            inserts.append((ln, [f"{indent}{marker} {c}" for c in cs], (m.path, fn.name)))
        shift = 0
        for ln, new, key in sorted(inserts, key=lambda x: x[0]):
            at = ln + shift
            lines[at:at] = new
            starts[key] = at + 1
            shift += len(new)
        dest = Path(work, m.path)
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_text("\n".join(lines) + "\n")
    # things the frontends need next to the sources (package markers, tsconfig)
    for extra in ("tsconfig.json", "package.json"):
        if os.path.exists(os.path.join(root, extra)) and not os.path.exists(os.path.join(work, extra)):
            shutil.copy(os.path.join(root, extra), os.path.join(work, extra))
    for m in modules:
        d = Path(root, m.path).parent
        while str(d).startswith(root) and (d / "__init__.py").exists():
            rel = d.relative_to(root) / "__init__.py"
            if not Path(work, rel).exists():
                Path(work, rel).parent.mkdir(parents=True, exist_ok=True)
                shutil.copy(d / "__init__.py", Path(work, rel))
            d = d.parent
    return starts


# ---------------------------------------------------------------------------
# The loop


def propose(paths: list[str], root: str, opts: Any, only: set[str] | None = None, progress: Any = None) -> list[Proposal]:
    from .checker import check_modules, load_modules
    from .program import Program

    root = os.path.abspath(root)
    modules = load_modules(paths, root)
    program = Program.build(modules)
    base_opts = _quiet(opts)
    targets: list[tuple[ir.Module, ir.Function]] = [
        (m, fn) for m in modules if not m.context for fn in m.functions.values() if not (only and fn.name not in only) and not fn.trusted and not fn.unit
    ]
    props: dict[tuple[str, str], Proposal] = {}
    for m, fn in targets:
        p = Proposal(m.path, fn.name, m.language, fn.loc.line, fn.end_line)
        if fn.unsupported:
            p.skipped = fn.unsupported[0][0]
        props[(m.path, fn.name)] = p

    # 0. what can crash as the code stands
    base = check_modules(load_modules(paths, root), base_opts, root=root)
    crashes: dict[tuple[str, str], list[str]] = {}
    for f in base.functions:
        key = (f.ref.module.path, f.fn.name)
        bad = list(dict.fromkeys(f"{_kind(v.ob.kind)} at line {v.ob.loc.line}" for v in f.verdicts if v.ob.kind in CRASH_KINDS and v.status != "proved"))
        if bad and key in props:
            crashes[key] = bad
            props[key].crashes = bad

    # 1. Houdini over candidate postconditions
    cands = {k: [f"ensures {c}" for c in ensures_candidates(fn, program, m.language) if _norm(c) not in _stated(fn, program)] for m, fn in targets if not fn.unsupported and (k := (m.path, fn.name))}
    cands = {k: v for k, v in cands.items() if v}
    for rnd in range(MAX_ROUNDS):
        if not cands:
            break
        if progress:
            progress(f"checking {sum(len(v) for v in cands.values())} candidate facts (round {rnd + 1})")
        status = _run(root, modules, cands, base_opts)
        failed = False
        for key, cs in list(cands.items()):
            st = status.get(key, {})
            keep = [c for c in cs if st.get(c[len("ensures ") :]) == "proved"]
            if len(keep) != len(cs):
                failed = True
            cands[key] = keep
        cands = {k: v for k, v in cands.items() if v}
        if not failed:
            break
    stated = {(m.path, fn.name): _stated(fn, program) for m, fn in targets}
    for key, cs in cands.items():
        props[key].facts = _prune(cs, stated.get(key, set()))

    # 2. preconditions that remove every crash, one candidate at a time
    reqs = {key: requires_candidates(fn, m.language) for m, fn in targets if (key := (m.path, fn.name)) in crashes and not fn.unsupported}
    depth = max((len(v) for v in reqs.values()), default=0)
    for i in range(depth):
        trial = {k: [f"requires {v[i]}"] for k, v in reqs.items() if i < len(v)}
        if not trial:
            break
        if progress:
            progress(f"trying preconditions ({i + 1}/{depth})")
        rep = _run(root, modules, trial, base_opts, crashes_of=True)
        for key, [c] in trial.items():
            left = rep.get(key, {}).get("__crashes__")
            if left is not None and not left:
                subject = re.split(r"[\s.<>=!(]", c[len("requires ") :].replace("0 <= ", ""), 1)[0]
                if any(re.split(r"[\s.<>=!(]", f[len("requires ") :].replace("0 <= ", ""), 1)[0] == subject for f, _ in props[key].fixes):
                    continue  # a weaker condition on the same value already works (candidates go weakest first)
                props[key].fixes.append((c, crashes[key]))
    return [p for p in props.values()]


def _norm(text: str) -> str:
    """Spacing and the names of generator variables do not matter."""
    text = re.sub(r"\s+", " ", text.strip())
    for v in re.findall(r"\bfor (\w+) in\b", text):
        text = re.sub(rf"\b{v}\b", "_", text)
    return text.replace(" ", "")


def _stated(fn: ir.Function, program: Any) -> set[str]:
    """What the contract already says: its @ensures, and for a method the
    invariants of its class (both as written)."""
    out = {_norm(c.text) for c in fn.ensures}
    self_p = next((p for p in fn.params if p.name in ("self", "this")), None)
    if self_p is not None and isinstance(self_p.ty, ir.TClass):
        for cls in program.mro(self_p.ty.name) if self_p.ty.name in program.classes else []:
            out |= {_norm(c.text) for c in program.classes[cls].invariants}
    return out


def _kind(k: str) -> str:
    return {"div": "division by zero", "index": "index out of bounds", "none": "None used as a value", "key": "missing key", "overflow": "overflow"}.get(k, k)


def _prune(cs: list[str], stated: set[str] = frozenset()) -> list[str]:  # type: ignore[assignment]
    """Drop facts another kept or already stated fact implies (x > 0 makes
    x >= 0 redundant, == makes <= and >= redundant). ``stated`` is
    normalized (see _norm)."""
    known = {_norm(c[len("ensures ") :]) for c in cs} | set(stated)
    out = []
    for c in cs:
        t = c[len("ensures ") :]
        m = re.fullmatch(r"(.+?) (>=|<=) (.+)", t)
        if m and (_norm(f"{m.group(1)} == {m.group(3)}") in known or _norm(f"{m.group(1)} === {m.group(3)}") in known):
            continue
        if m and m.group(2) == ">=" and _norm(f"{m.group(1)} > {m.group(3)}") in known:
            continue
        if m and m.group(2) == "<=" and _norm(f"{m.group(1)} < {m.group(3)}") in known:
            continue
        out.append(c)
    return out


def _quiet(opts: Any) -> Any:
    import dataclasses

    return dataclasses.replace(opts, cache_path=None, lean=False, replay=False, receipts=False, progress=None)


def _run(root: str, modules: list[ir.Module], clauses: dict[tuple[str, str], list[str]], opts: Any, crashes_of: bool = False) -> dict[tuple[str, str], dict[str, Any]]:
    """Check a scratch copy with ``clauses`` inserted; per function, the status
    of each inserted clause (and, with ``crashes_of``, the crashes left)."""
    from .checker import check_modules, load_modules

    work = tempfile.mkdtemp(prefix="telic-propose-")
    try:
        write_scratch(root, modules, clauses, work)
        paths = [os.path.join(work, m.path) for m in modules if not m.context]
        rep = check_modules(load_modules(paths, work), opts, root=work)
    finally:
        pass
    out: dict[tuple[str, str], dict[str, Any]] = {}
    for f in rep.functions:
        key = (f.ref.module.path, f.fn.name)
        st: dict[str, Any] = {}
        texts = {" ".join(c.split(None, 1)[1].split()) if " " in c else c for c in clauses.get(key, [])}
        for v in f.verdicts:
            if v.ob.clause is not None and v.ob.clause.text in texts:
                prev = st.get(v.ob.clause.text)
                st[v.ob.clause.text] = v.status if prev in (None, "proved") else prev
        # a clause that could not even be expressed is not a fact
        if f.status in ("unsupported", "error"):
            st = {}
        if crashes_of:
            st["__crashes__"] = [v.ob.id for v in f.verdicts if v.ob.kind in CRASH_KINDS and v.status != "proved"] if f.status not in ("unsupported", "error") else None
        out[key] = st
    shutil.rmtree(work, ignore_errors=True)
    return out


# ---------------------------------------------------------------------------
# Writing accepted clauses back


def write_back(root: str, props: list[Proposal], with_fixes: bool) -> int:
    from .checker import load_modules

    by_file: dict[str, list[Proposal]] = {}
    for p in props:
        by_file.setdefault(p.module, []).append(p)
    n = 0
    for path, ps in by_file.items():
        full = os.path.join(root, path)
        mods = load_modules([full], root)
        m = mods[-1]
        src = Path(full).read_text()
        lines = src.splitlines()
        inserts = []
        for p in ps:
            fn = m.functions.get(p.func)
            clauses = list(p.facts) + ([p.fixes[0][0]] if with_fixes and p.fixes else [])
            if fn is None or not clauses:
                continue
            pt = insertion_point(src, fn, m.language)
            if pt is None:
                continue
            ln, indent = pt
            marker = "#@" if m.language == "python" else "//@"
            inserts.append((ln, [f"{indent}{marker} {c}" for c in clauses]))
            n += len(clauses)
        for ln, new in sorted(inserts, key=lambda x: -x[0]):
            lines[ln:ln] = new
        Path(full).write_text("\n".join(lines) + ("\n" if src.endswith("\n") else ""))
    return n


# ---------------------------------------------------------------------------
# Drafting aims (an oracle's classification of proved facts, never a proof)

KIND_CRITERIA = {
    "requirement": "a behaviour a product owner would state as a requirement of the system",
    "detail": "true, but an implementation detail, a type-level range or a frame condition nobody would write down as a requirement",
    "bug": "looks wrong: no sensible product wants this behaviour, so the code probably has a bug",
}


def draft_aims(props: list[Proposal], root: str, oracle: str | None = None, k: int = 6) -> dict[str, Any]:
    """Draft EARS aims from the proved facts. Every draft starts as a
    literal rendering of one proved clause (``phrase.requirement``); the
    oracle classifies each as a requirement, a detail or a likely bug, and a
    generative oracle may rephrase it and name requirements nothing proves
    yet. Drafts that cite facts only ever cite facts telic proved."""
    from . import oracle as oracles
    from .aim import ears_problems
    from .phrase import requirement

    facts: dict[str, tuple[Proposal, str]] = {}
    sources: dict[str, str] = {}
    for p in props[:80]:
        clauses = p.facts + [f for f, _ in p.fixes[:1]]
        if not clauses:
            continue
        sources[p.func] = _function_source(root, p)
        for c in clauses:
            facts[f"F{len(facts) + 1}"] = (p, c)
    if not facts:
        return {"aims": [], "unbacked": [], "suspicious": [], "details": [], "facts": {}, "oracle": None, "notes": []}
    literal = {fid: requirement(p.func, c) for fid, (p, c) in facts.items()}
    state = {
        "functions": sources,
        "candidates": {
            fid: {"function": p.func, "clause": c, "sentence": literal[fid], "proved": True, "needed_to_be_crash_free": c.startswith("requires")}
            for fid, (p, c) in facts.items()
        },
        "note": "Each candidate is a fact a static verifier proved about the function as written. A fact can faithfully describe a bug.",
    }
    questions: dict[str, Any] = {}
    for fid in facts:
        questions[f"{fid}_kind"] = {
            "type": "choice",
            "instructions": f"Candidate {fid}: \"{literal[fid]}\" (from `{facts[fid][1]}` on {facts[fid][0].func}). What is it?",
            "criteria": KIND_CRITERIA,
        }
        questions[f"{fid}_phrase"] = {
            "type": "text",
            "instructions": f"Rewrite candidate {fid} as one EARS requirement a product owner would recognise (exactly one 'shall'; start with The / WHEN / WHILE / IF ... THEN / WHERE). Keep its meaning; do not claim more than the fact.",
        }
    questions["gaps"] = {
        "type": "text",
        "instructions": f"List up to {k} requirements the code clearly aims at that no candidate establishes, as a JSON array of EARS sentences.",
    }
    got = oracles.consult("classify-facts", state, questions, spec=oracle, root=root)
    ans = got.answers

    ranked = []
    suspicious = []
    details: list[str] = []
    for fid, (p, c) in facts.items():
        a = ans.get(f"{fid}_kind") or {}
        kind = a.get("choice", "requirement")
        conf = a.get("confidence")
        if kind == "bug":
            suspicious.append({"fact": fid, "why": f"classified as a likely bug by {a.get('by', got.oracle)}" + (f" (p={conf:.2f})" if isinstance(conf, (int, float)) else "")})
        if kind == "detail":
            details.append(fid)
        if kind != "requirement":
            continue
        text = literal[fid]
        phrased = (ans.get(f"{fid}_phrase") or {}).get("text")
        if phrased and not ears_problems(phrased):
            text = " ".join(phrased.split())
        ranked.append((-(conf if isinstance(conf, (int, float)) else 0.5), fid, text, a.get("by", got.oracle)))
    ranked.sort()
    aims = []
    seen: set[str] = set()
    for _, fid, text, by in ranked[:k]:
        p = facts[fid][0]
        base = re.sub(r"[^A-Z0-9]+", "-", p.func.split(".")[-1].upper()).strip("-") or "AIM"
        iid, n = base, 2
        while iid in seen:
            iid, n = f"{base}-{n}", n + 1
        seen.add(iid)
        aims.append({"id": iid, "text": text, "facts": [fid], "lint": ears_problems(text), "by": by})
    unbacked = []
    gaps = (ans.get("gaps") or {}).get("text")
    for sentence in _sentences(gaps):
        wid = "-".join(w.upper() for w in re.findall(r"[A-Za-z]+", sentence) if w.lower() not in ("when", "the", "shall", "a", "an", "if", "then", "while", "where", "system"))[:40].strip("-")
        unbacked.append({"id": wid or "AIM", "text": sentence, "facts": [], "lint": ears_problems(sentence), "by": ans["gaps"].get("by", got.oracle)})
    return {
        "aims": aims,
        "unbacked": unbacked,
        "suspicious": suspicious,
        "details": details,
        "facts": {fid: {"func": p.func, "module": p.module, "clause": c} for fid, (p, c) in facts.items()},
        "oracle": got.oracle,
        "notes": got.notes,
    }


def _sentences(text: str | None) -> list[str]:
    if not text:
        return []
    m = re.search(r"\[.*\]", text, re.S)
    if m:
        try:
            return [" ".join(str(x).split()) for x in json.loads(m.group(0)) if str(x).strip()]
        except ValueError:
            pass
    return [" ".join(x.lstrip("-* ").split()) for x in text.splitlines() if "shall" in x.lower()]


def _function_source(root: str, p: Proposal) -> str:
    try:
        lines = Path(root, p.module).read_text().splitlines()
    except OSError:
        return ""
    start = p.line - 1
    return "\n".join(lines[start : max(p.end_line, p.line)][:60])


# ---------------------------------------------------------------------------
# CLI


def cmd_propose(args: Any, options: Any) -> int:
    from .render import Paint

    root = os.path.abspath(args.root or os.getcwd())
    opts = options(args, root)
    color = getattr(args, "color", "auto")
    p = Paint(None if color == "auto" else color == "always")
    only = set(args.only) if args.only else None
    say = (lambda msg: print(p.dim(f"  … {msg}"), flush=True)) if not args.json else None
    props = propose(args.paths, root, opts, only=only, progress=say)
    drafted = None
    if args.aims:
        try:
            drafted = draft_aims(props, root, oracle=args.oracle)
        except Exception as e:  # noqa: BLE001 - reported, the facts still stand
            drafted = {"error": str(e)}
    if args.json:
        print(json.dumps({
            "functions": [{"module": x.module, "function": x.func, "facts": x.facts, "crashes": x.crashes, "fixes": [{"requires": r, "removes": c} for r, c in x.fixes], "skipped": x.skipped} for x in props],
            "aims": drafted,
        }, indent=2))
    else:
        print(render_proposals(props, drafted, p))
    if args.write:
        n = write_back(root, props, with_fixes=args.with_fixes)
        print(p.green(f"wrote {n} clause{'s' * (n != 1)}") + p.dim("  (run telic check to see them proved)"))
    return 0


def render_proposals(props: list[Proposal], drafted: dict[str, Any] | None, p: Any) -> str:
    out = []
    shown = [x for x in props if x.facts or x.fixes or x.crashes]
    if not shown:
        return p.dim("nothing to propose: no checkable function has a provable fact or a crash to rule out")
    out.append(p.bold("Facts telic proved about the code as it is") + p.dim("  (true whenever the function returns; you decide whether each is intended)"))
    out.append("")
    for x in shown:
        marker = "#@" if x.language == "python" else "//@"
        out.append(f"  {p.bold(x.func)} {p.dim(f'{x.module}:{x.line}')}")
        frame = [c for c in x.facts if re.fullmatch(r"ensures (self|this)\.(\w+) ={2,3} old\(\1\.\2\)", c)]
        if len(frame) > 2:
            fields = ", ".join(re.search(r"\.(\w+) ", c).group(1) for c in frame)  # type: ignore[union-attr]
            out.append(f"    {p.green(marker)} {p.dim(f'leaves {fields} unchanged ({len(frame)} facts)')}")
        for c in x.facts:
            if len(frame) > 2 and c in frame:
                continue
            out.append(f"    {p.green(marker)} {c}")
        if x.crashes:
            out.append(f"    {p.red('can crash:')} {', '.join(x.crashes)}")
            if x.fixes:
                for r, _ in x.fixes[:3]:
                    out.append(f"    {p.yellow(marker)} {r}   {p.dim('removes every crash; callers must then establish it')}")
            else:
                out.append(p.dim("    no single simple precondition removes it: fix the code, or state one by hand"))
        out.append("")
    if drafted is not None:
        if "error" in drafted:
            out.append(p.yellow(f"aims: could not draft ({drafted['error']})"))
        else:
            out.append(p.bold("Draft aims") + p.dim(f"  (proved facts in words, sorted by {drafted.get('oracle') or 'an oracle'}: requirements are yours to decide)"))
            out.append("")
            facts = drafted.get("facts", {})
            for it in drafted.get("aims", []):
                by = sorted({facts[f]["func"] for f in it["facts"]})
                out.append(f"  #@ aim {it['id']}: {it['text']}")
                out.append(f"  #@   by: {', '.join(by)}")
                out.append(p.dim("    backed by these lemmas, cited in their functions:"))
                for f in it["facts"]:
                    out.append(f"      {p.dim(facts[f]['func'] + ':')} #@ [{it['id']}] {facts[f]['clause']}")
                for lint in it["lint"]:
                    out.append(p.yellow(f"      EARS: {lint}"))
                out.append("")
            if drafted.get("unbacked"):
                out.append(p.bold("Draft aims nothing proves yet") + p.dim("  (decide whether each is a requirement; then write the lemmas that back it)"))
                out.append("")
                for it in drafted["unbacked"]:
                    out.append(f"  #@ aim {it['id']}: {it['text']}")
                    for lint in it["lint"]:
                        out.append(p.yellow(f"      EARS: {lint}"))
                out.append("")
            for s in drafted.get("suspicious", []):
                f = facts.get(s["fact"], {})
                out.append(p.red(f"  suspicious: {f.get('func')}: {f.get('clause')}") + p.dim(f" -- {s.get('why', '')}"))
            if drafted.get("details"):
                n = len(drafted["details"])
                out.append(p.dim(f"  {n} fact{'s' * (n != 1)} read as implementation detail{'s' * (n != 1)}, not drafted"))
            for n in drafted.get("notes", []):
                out.append(p.dim(f"  oracle: {n}"))
    return "\n".join(out)


def add_command(sub: Any, common: Any, options: Any) -> None:
    c = sub.add_parser("propose", help="propose contracts (proved facts, crash-free preconditions) and draft aims for code without them")
    common(c)
    c.add_argument("--color", choices=["auto", "always", "never"], default="auto")
    c.add_argument("--aims", action="store_true", help="also draft EARS aims from the proved facts (classified by the oracle)")
    c.add_argument("--oracle", default=None, help="oracle spec (builtin, jev, anthropic, cmd:..., http:..., py:...; default TELIC_ORACLE)")
    c.add_argument("--write", action="store_true", help="insert the proved facts into the source")
    c.add_argument("--with-fixes", action="store_true", help="with --write, also insert the first crash-free precondition")
    c.add_argument("--json", action="store_true")
    c.set_defaults(func=lambda a: cmd_propose(a, options))
