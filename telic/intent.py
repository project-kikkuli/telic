"""Intents: top-level requirements, backed by lemmas one layer below.

An intent is a requirement a reviewer can read, one EARS sentence:

    #@ intent REFUND-CAP: WHEN a refund is issued, the system shall never
    #@   refund more than was paid, net of earlier refunds.
    #@   by: refund, Ledger.apply, web/checkout.ts::refundButton

It is not a formula and telic never calls it "proved". What telic proves
are lemmas: contract clauses on functions anywhere in the project (either
language) that cite the intent -- ``#@ intent REFUND-CAP`` above a function
tags its clauses, ``#@ [REFUND-CAP] ensures ...`` tags one. The ``by:`` list
points down from the intent to its lemmas; citations point back up. Both
directions are checked, so neither side can drift silently.

An intent's status says what its lemmas establish:

    backed    every lemma is proved (and so is everything they rest on)
    broken    a lemma is refuted: the code contradicts part of the requirement
    partial   some lemma is open or its function is not checkable
    unbacked  declared, but no lemma cites it
    undeclared cited, but never declared

Whether the lemmas *cover* the requirement is a separate question that no
prover answers. It is recorded separately, as a human review (pinned to the
exact intent text and lemma set, so it goes stale when either changes) or as
a cheap model's judgment (cached by the same hash, always labelled
"judged").
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import subprocess
import time
from dataclasses import dataclass, field
from typing import Any

# ---------------------------------------------------------------------------
# EARS


_EARS_START = ("the ", "when ", "while ", "if ", "where ")


def ears_problems(text: str) -> list[str]:
    """Shape problems of an intent sentence against the EARS patterns
    (ubiquitous, WHEN, WHILE, IF/THEN, WHERE and their combinations). A lint,
    not a parser: it keeps requirements in one reviewable form."""
    t = " ".join(text.split())
    low = t.lower()
    out: list[str] = []
    shalls = len(re.findall(r"\bshall\b", low))
    if shalls == 0:
        out.append("has no 'shall': state the required response ('the <system> shall ...')")
    elif shalls > 1:
        out.append("has more than one 'shall': split it into one intent per requirement")
    if not low.startswith(_EARS_START):
        out.append("should start with WHEN / WHILE / IF / WHERE or 'The <system> shall'")
    if low.startswith("if ") and not re.search(r"\bthen\b", low):
        out.append("an IF requirement needs THEN before the response")
    body = t.rstrip(".")
    if re.search(r"[.!?]\s+[A-Z]", body):
        out.append("is more than one sentence")
    return out


def split_by(text: str) -> tuple[str, list[str]]:
    """``sentence by: a, b`` -> (sentence, [a, b])."""
    m = re.match(r"^(.*?)\s*\bby:\s*(.+)$", " ".join(text.split()))
    if not m:
        return " ".join(text.split()), []
    items = [x.strip().rstrip(".") for x in m.group(2).split(",")]
    return m.group(1).strip(), [x for x in items if x]


# ---------------------------------------------------------------------------
# Reports


@dataclass
class Lemma:
    func: str  # FuncRef key
    name: str  # function name as written
    path: str
    line: int
    kind: str  # ensures | raises | invariant | mirror
    text: str
    status: str  # proved | refuted | open | trusted | unsupported


@dataclass
class IntentReport:
    id: str
    text: str | None
    loc: tuple[str, int] | None
    functions: list[str]
    status: str  # backed | broken | partial | unbacked | undeclared
    by: list[str] = field(default_factory=list)
    lemmas: list[Lemma] = field(default_factory=list)
    pointers: list[str] = field(default_factory=list)  # two-sided link problems
    ears: list[str] = field(default_factory=list)
    coverage: dict[str, Any] | None = None  # review / judgment
    digest: str = ""  # hash of the text and the lemma set

    # counts kept for the ledger and older callers
    @property
    def proved(self) -> int:
        return sum(1 for x in self.lemmas if x.status in ("proved", "trusted"))

    @property
    def refuted(self) -> int:
        return sum(1 for x in self.lemmas if x.status == "refuted")

    @property
    def open(self) -> int:
        return sum(1 for x in self.lemmas if x.status not in ("proved", "trusted", "refuted"))

    @property
    def clauses(self) -> int:
        return len(self.lemmas)


def _match(item: str, key: str, name: str) -> bool:
    """Does a ``by:`` item name this function? ``name``, ``Class.method``,
    or ``path::name`` (path may be a suffix of the module path)."""
    if "::" in item:
        p, n = item.rsplit("::", 1)
        return n == name and key.split("::")[0].endswith(p)
    return item == name


def build(rep: Any) -> list[IntentReport]:
    decls: dict[str, tuple[str, tuple[str, int], list[str]]] = {}
    for m in rep.modules:
        for d in m.intents:
            text, by = split_by(d.text)
            if d.id in decls:
                old = decls[d.id]
                decls[d.id] = (old[0], old[1], old[2] + [b for b in by if b not in old[2]])
            else:
                decls[d.id] = (text, (m.path, d.loc.line), by)
    citing: dict[str, list[Any]] = {}
    for f in rep.functions:
        for i in f.fn.intents:
            citing.setdefault(i, []).append(f)
    mirrors: dict[str, list[Any]] = {}
    for mr in rep.mirrors:
        for i in mr.intents:
            mirrors.setdefault(i, []).append(mr)
    reviews = _load_reviews(getattr(rep, "root", None))
    out: list[IntentReport] = []
    for iid in sorted(set(decls) | set(citing) | set(mirrors)):
        text, loc, by = decls.get(iid, (None, None, []))
        fns = citing.get(iid, [])
        r = IntentReport(iid, text, loc, [f.ref.key for f in fns], "partial", by=by)
        for f in fns:
            clauses = [c for c in f.fn.ensures + f.fn.raises if iid in c.intents]
            for s in _loop_invariants(f.fn):
                if iid in s.intents:
                    clauses.append(s)
            if not clauses:
                r.pointers.append(f"{f.fn.name} cites {iid} but none of its @ensures carries it")
            for c in clauses:
                r.lemmas.append(Lemma(f.ref.key, f.fn.name, f.ref.module.path, c.loc.line, c.kind, c.text, _clause_status(f, c)))
        for mr in mirrors.get(iid, []):
            st = {"proved": "proved", "refuted": "refuted"}.get(mr.status, "open")
            r.lemmas.append(Lemma(mr.a.key, f"{mr.a.fn.name} ≡ {mr.b.fn.name}", mr.a.module.path, mr.a.fn.loc.line, "mirror", "agree on every input", st))
        # Two-sided pointers.
        if by:
            for item in by:
                hit = [f for f in rep.functions if _match(item, f.ref.key, f.fn.name)]
                if not hit:
                    r.pointers.append(f"'{item}' is listed in by: but no checked function has that name")
                elif not any(iid in f.fn.intents for f in hit):
                    r.pointers.append(f"'{item}' is listed in by: but does not cite {iid}")
            for f in fns:
                if not any(_match(item, f.ref.key, f.fn.name) for item in by):
                    r.pointers.append(f"{f.fn.name} cites {iid} but is not in its by: list")
        if text is not None:
            r.ears = ears_problems(text)
        # Status: what the lemmas establish (never "proved").
        fstat = [f.status for f in fns] + [m.status for m in mirrors.get(iid, [])]
        if text is None:
            r.status = "undeclared"
        elif not r.lemmas:
            r.status = "unbacked"
        elif "refuted" in fstat or any(x.status == "refuted" for x in r.lemmas):
            r.status = "broken"
        elif all(s in ("proved", "trusted") for s in fstat) and all(x.status in ("proved", "trusted") for x in r.lemmas) and not any(f.open_deps for f in fns):
            r.status = "backed"
        else:
            r.status = "partial"
        r.digest = digest(r)
        rv = reviews.get(iid)
        if rv is not None:
            r.coverage = {"kind": "reviewed", "by": rv.get("by", ""), "fresh": rv.get("digest") == r.digest}
        out.append(r)
    return out


def _loop_invariants(fn: Any):
    from . import ir

    for s in ir.walk_stmts(fn.body):
        if isinstance(s, (ir.While, ir.ForRange, ir.ForEach)):
            yield from s.invariants


def _clause_status(f: Any, c: Any) -> str:
    if f.status in ("unsupported", "error"):
        return "unsupported"
    if f.status == "trusted":
        return "trusted"
    vs = [v for v in f.verdicts if v.ob.clause is c or (v.ob.clause is not None and v.ob.clause.loc == c.loc and v.ob.clause.text == c.text)]
    if not vs:
        return "proved" if f.status == "proved" else "open"
    if any(v.status == "refuted" for v in vs):
        return "refuted"
    if all(v.status == "proved" for v in vs):
        return "proved"
    return "open"


def digest(r: IntentReport) -> str:
    """What a review or judgment is about: the sentence and the lemma set."""
    h = hashlib.sha256()
    h.update((r.text or "").encode())
    for x in sorted((x.name, x.kind, x.text) for x in r.lemmas):
        h.update(("\0" + "\0".join(x)).encode())
    return h.hexdigest()[:16]


# ---------------------------------------------------------------------------
# Reviews (human) -- stored in the committed ledger

REVIEWS = "telic.reviews.json"


def _load_reviews(root: str | None) -> dict[str, Any]:
    path = os.path.join(root or ".", REVIEWS)
    try:
        with open(path) as fh:
            return json.load(fh)
    except (OSError, ValueError):
        return {}


def accept(root: str, r: IntentReport, who: str) -> None:
    """Record that a person reviewed this intent's lemmas and found they
    cover it. Pinned to the digest: any change to the sentence or the lemma
    set makes the review stale."""
    data = _load_reviews(root)
    data[r.id] = {"digest": r.digest, "by": who, "at": time.strftime("%Y-%m-%d")}
    with open(os.path.join(root, REVIEWS), "w") as fh:
        json.dump(data, fh, indent=2, sort_keys=True)
        fh.write("\n")


# ---------------------------------------------------------------------------
# Judgments (a cheap model) -- cached by digest, never trusted as proof

JUDGE_CACHE = os.path.join(".telic", "judgments.json")
DEFAULT_MODEL = "claude-haiku-4-5-20251001"


def judge_prompt(r: IntentReport) -> str:
    facts = "\n".join(f"- {x.name} ({x.path}:{x.line}), {x.kind}: {x.text}  [{x.status}]" for x in r.lemmas)
    return (
        "You are reviewing whether facts proved about a codebase establish one of its requirements.\n\n"
        f"Requirement ({r.id}): {r.text}\n\n"
        "Proved facts (each is a contract clause on the named function, checked by a static verifier; "
        "the bracket says whether it was proved):\n"
        f"{facts}\n\n"
        "Taken together, do the proved facts establish the requirement? Every condition the requirement "
        "imposes must be covered by some fact; facts about unrelated behaviour do not count. "
        "Answer on the first line with exactly SUFFICIENT or INSUFFICIENT, and on the second line name "
        "what is missing (or 'nothing')."
    )


def judge(root: str, reports: list[IntentReport], model: str | None = None, command: str | None = None) -> list[str]:
    """Ask a cheap model whether each intent's lemmas cover it. Returns
    messages about anything that could not be judged."""
    model = model or os.environ.get("TELIC_JUDGE_MODEL") or DEFAULT_MODEL
    command = command or os.environ.get("TELIC_JUDGE_CMD")
    path = os.path.join(root, JUDGE_CACHE)
    try:
        with open(path) as fh:
            cache = json.load(fh)
    except (OSError, ValueError):
        cache = {}
    notes: list[str] = []
    for r in reports:
        if r.text is None or not r.lemmas:
            continue
        key = f"{model if not command else 'cmd:' + command}:{r.digest}"
        if key not in cache:
            prompt = judge_prompt(r)
            try:
                answer = _ask(prompt, model, command)
            except Exception as e:  # network, no key, bad command
                notes.append(f"{r.id}: not judged ({e})")
                continue
            lines = [x.strip() for x in answer.strip().splitlines() if x.strip()]
            verdict = "sufficient" if lines and lines[0].upper().startswith("SUFFICIENT") else "insufficient"
            cache[key] = {"verdict": verdict, "missing": lines[1] if len(lines) > 1 else "", "model": model if not command else command}
        j = cache[key]
        if r.coverage is None or r.coverage.get("kind") != "reviewed" or not r.coverage.get("fresh"):
            r.coverage = {"kind": "judged", **j}
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w") as fh:
        json.dump(cache, fh, indent=2, sort_keys=True)
    return notes


def attach_cached_judgments(root: str, reports: list[IntentReport]) -> None:
    """Show judgments already made for exactly this text and lemma set."""
    try:
        with open(os.path.join(root, JUDGE_CACHE)) as fh:
            cache = json.load(fh)
    except (OSError, ValueError):
        return
    for r in reports:
        if r.coverage is not None and r.coverage.get("kind") == "reviewed" and r.coverage.get("fresh"):
            continue
        for key, j in cache.items():
            if key.endswith(":" + r.digest):
                r.coverage = {"kind": "judged", **j}
                break


def _ask(prompt: str, model: str, command: str | None) -> str:
    if command:
        p = subprocess.run(command, shell=True, input=prompt, capture_output=True, text=True, timeout=120)
        if p.returncode != 0:
            raise RuntimeError(f"judge command failed: {p.stderr.strip()[-200:]}")
        return p.stdout
    key = os.environ.get("ANTHROPIC_API_KEY")
    if not key:
        raise RuntimeError("set ANTHROPIC_API_KEY, or TELIC_JUDGE_CMD to a command that reads the prompt on stdin")
    import urllib.request

    body = json.dumps({"model": model, "max_tokens": 200, "messages": [{"role": "user", "content": prompt}]}).encode()
    req = urllib.request.Request(
        "https://api.anthropic.com/v1/messages",
        data=body,
        headers={"x-api-key": key, "anthropic-version": "2023-06-01", "content-type": "application/json"},
    )
    with urllib.request.urlopen(req, timeout=60) as resp:
        data = json.loads(resp.read())
    return "".join(part.get("text", "") for part in data.get("content", []))


# ---------------------------------------------------------------------------
# CLI: telic intents


def cmd_intents(args: Any, options: Any) -> int:
    from .checker import check
    from .render import Paint, Renderer

    root = os.path.abspath(args.root or os.getcwd())
    rep = check(args.paths, options(args, root), root=root)
    notes: list[str] = []
    if args.accept:
        who = args.who or os.environ.get("USER") or "reviewer"
        for iid in args.accept:
            r = next((x for x in rep.intents if x.id == iid), None)
            if r is None:
                print(f"telic: no intent {iid}")
                return 2
            if r.status != "backed":
                print(f"telic: {iid} is {r.status}; only a backed intent's coverage can be reviewed")
                return 1
            accept(root, r, who)
            r.coverage = {"kind": "reviewed", "by": who, "fresh": True}
            print(f"reviewed {iid} ({len(r.lemmas)} lemmas, digest {r.digest}) -> {REVIEWS}")
    if args.judge:
        notes = judge(root, rep.intents)
    if args.json:
        print(json.dumps([_intent_json(r) for r in rep.intents], indent=2))
    else:
        paint = Paint(None)
        print("\n".join(Renderer(rep, paint).intent_table()))
        for n in notes:
            print(paint.dim("  " + n))
    bad = [r for r in rep.intents if r.status in ("broken", "undeclared") or r.pointers]
    return 1 if bad else 0


def _intent_json(r: IntentReport) -> dict[str, Any]:
    return {
        "id": r.id,
        "text": r.text,
        "status": r.status,
        "at": f"{r.loc[0]}:{r.loc[1]}" if r.loc else None,
        "by": r.by,
        "lemmas": [{"function": x.name, "at": f"{x.path}:{x.line}", "kind": x.kind, "text": x.text, "status": x.status} for x in r.lemmas],
        "links": r.pointers,
        "ears": r.ears,
        "coverage": r.coverage,
        "digest": r.digest,
    }


def add_commands(sub: Any, common: Any, options: Any) -> None:
    i = sub.add_parser("intents", help="requirements, the lemmas backing them, and whether their links hold")
    common(i)
    i.add_argument("--judge", action="store_true", help="ask a cheap model whether each intent's lemmas cover it (cached)")
    i.add_argument("--accept", nargs="+", metavar="ID", help="record that you reviewed these intents' lemmas and they cover the requirement")
    i.add_argument("--as", dest="who", help="reviewer name for --accept")
    i.add_argument("--json", action="store_true")
    i.set_defaults(func=lambda a: cmd_intents(a, options))
