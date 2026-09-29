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
    scope: str | None = None  # declared in <scope>/intents.md ('' = the root); None = a comment
    advice: list[str] = field(default_factory=list)  # findings that do not fail

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
    from .frontend.intents_md import LANGUAGE, scope_of

    decls: dict[str, tuple[str, tuple[str, int], list[str], str | None, bool]] = {}
    twice: dict[str, list[str]] = {}
    for m in sorted(rep.modules, key=lambda m: m.language == LANGUAGE and m.context):
        scope = scope_of(m.path) if m.language == LANGUAGE else None
        for d in m.intents:
            text, by = split_by(d.text)
            if d.id in decls:
                twice.setdefault(d.id, []).append(f"{m.path}:{d.loc.line}")
            else:
                decls[d.id] = (text, (m.path, d.loc.line), by, scope, m.context and scope is not None)
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
    shown = {k for k, d in decls.items() if not d[4]} | set(citing) | set(mirrors)
    for iid in sorted(shown):
        text, loc, by, scope, context = decls.get(iid, (None, None, [], None, False))
        fns = citing.get(iid, [])
        r = IntentReport(iid, text, loc, [f.ref.key for f in fns], "partial", by=by, scope=scope)
        if iid in twice and loc is not None:
            r.pointers.append(f"{iid} is declared more than once ({loc[0]}:{loc[1]}, {', '.join(twice[iid])}): keep one declaration")
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
                    if not context:  # an ancestor intents.md may list code outside this check
                        r.pointers.append(f"'{item}' is listed in by: but no checked function has that name")
                elif not any(iid in f.fn.intents for f in hit):
                    r.pointers.append(f"'{item}' is listed in by: but does not cite {iid}")
            for f in fns:
                if not any(_match(item, f.ref.key, f.fn.name) for item in by):
                    r.pointers.append(f"{f.fn.name} cites {iid} but is not in its by: list")
        if scope is not None:
            _check_scope(r, [f.ref.module.path for item in by for f in rep.functions if _match(item, f.ref.key, f.fn.name)], partial=context, root=getattr(rep, "root", None) or ".")
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
        elif any(x.status == "vacuous" for x in r.lemmas):
            r.status = "vacuous"
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


def _within(path: str, scope: str) -> bool:
    return not scope or path.replace(os.sep, "/").startswith(scope + "/")


def _inside(root: str, path: str, scope: str) -> bool:
    """Whether the file really lives under scope, through any symlinks."""
    real = os.path.realpath(os.path.join(root, scope))
    return os.path.realpath(os.path.join(root, path)).startswith(real + os.sep)


def _check_scope(r: IntentReport, targets: list[str], partial: bool, root: str) -> None:
    """A file-declared intent may only rest on code under its directory, and
    one whose lemmas all sit in one file belongs in that file (judged only
    when the check saw all of its code)."""
    scope = r.scope or ""
    home = f"{scope}/intents.md" if scope else "intents.md"
    outside = sorted({p for p in {x.path for x in r.lemmas} | set(targets) if not _inside(root, p, scope)})
    for path in outside:
        r.pointers.append(f"{path} is outside {scope or '.'}/, the scope of {home}: declare {r.id} in the intents.md of a directory containing both")
    files = {x.path for x in r.lemmas}
    if len(files) == 1 and not partial and not outside and set(targets) <= files:
        (only,) = files
        r.advice.append(f"every lemma is in {only}: declare {r.id} there as an '@intent {r.id}: ...' comment")


def _loop_invariants(fn: Any):
    from . import ir

    for s in ir.walk_stmts(fn.body):
        if isinstance(s, (ir.While, ir.ForRange, ir.ForEach)):
            yield from s.invariants


def _clause_status(f: Any, c: Any) -> str:
    if f.status in ("unsupported", "error"):
        return "unsupported"
    if f.status in ("trusted", "vacuous"):
        return f.status
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
# Judgments (an oracle: a classifier or a model) -- cached by digest, never proof

JUDGE_CACHE = os.path.join(".telic", "judgments.json")


def ears_conditions(text: str) -> tuple[str, list[str]]:
    """(trigger, response conditions) of an EARS sentence: "WHEN a refund is
    issued, the shop shall refund at most what was paid and log it" ->
    ("WHEN a refund is issued", ["the shop shall refund at most what was
    paid", "the shop shall log it"]). A split for asking about each part,
    not a grammar."""
    t = " ".join(text.split()).rstrip(".")
    m = re.match(r"^(?P<trig>(?:when|while|if|where)\b.*?)(?:,\s*|\s+then\s+)(?P<resp>[^,]*\bshall\b.*)$", t, re.I)
    trigger, response = (m.group("trig"), m.group("resp")) if m else ("", t)
    sm = re.match(r"^(?P<subj>.*?\bshall\b)\s+(?P<rest>.*)$", response, re.I)
    if not sm:
        return trigger, [response]
    subj, rest = sm.group("subj"), sm.group("rest")
    parts = [x.strip() for x in re.split(r",?\s+and\s+(?=[a-z]+\b)", rest) if x.strip()]
    return trigger, [f"{subj} {x}" for x in parts] or [response]


def coverage_request(r: IntentReport) -> tuple[dict[str, Any], dict[str, Any]]:
    trigger, conds = ears_conditions(r.text or "")
    state = {
        "requirement": r.text,
        "facts": [{"function": x.name, "clause": f"{x.kind} {x.text}", "status": x.status} for x in r.lemmas],
        "note": "Each fact is a contract clause on the named function, checked by a static verifier; status says whether it was proved. Only proved facts count.",
    }
    questions: dict[str, Any] = {
        "covers": {
            "type": "noul",
            "instructions": "Taken together, do the proved facts establish every condition the requirement imposes? Facts about unrelated behaviour do not count.",
            "criteria": {"true": "every condition of the requirement is established by some proved fact", "false": "some condition of the requirement is not established"},
        }
    }
    for i, c in enumerate(conds):
        sentence = f"{trigger}, {c}" if trigger else c
        questions[f"part{i + 1}"] = {
            "type": "noul",
            "instructions": f"Is this part of the requirement established by some proved fact: \"{sentence}\"?",
            "criteria": {"true": "a proved fact establishes it", "false": "no proved fact establishes it"},
            "condition": c,
        }
    return state, questions


def judge(root: str, reports: list[IntentReport], oracle: str | None = None) -> list[str]:
    """Ask the oracle whether each intent's lemmas cover it. Returns messages
    about anything that could not be judged. A review (``--accept``) always
    outranks a judgment."""
    from . import oracle as oracles

    path = os.path.join(root, JUDGE_CACHE)
    try:
        with open(path) as fh:
            cache = json.load(fh)
    except (OSError, ValueError):
        cache = {}
    chain = oracles.resolve(oracle, "coverage").name
    notes: list[str] = []
    for r in reports:
        if r.text is None or not r.lemmas:
            continue
        key = f"{chain}:{r.digest}"
        if key not in cache:
            state, questions = coverage_request(r)
            got = oracles.consult("coverage", state, questions, spec=oracle)
            notes += [f"{r.id}: {n}" for n in got.notes]
            p = oracles.noul(got.answers.get("covers"))
            if p is None:
                notes.append(f"{r.id}: not judged (no oracle answered)")
                continue
            parts = {k: q["condition"] for k, q in questions.items() if k != "covers"}
            weak = [c for k, c in parts.items() if (oracles.noul(got.answers.get(k)) or 0.0) < 0.5]
            cache[key] = {
                "verdict": "sufficient" if p >= 0.6 else "insufficient" if p <= 0.4 else "uncertain",
                "p": round(p, 2),
                "missing": "; ".join(weak) if weak else ("" if p >= 0.5 else "not named"),
                "model": got.answers["covers"].get("by", got.oracle),
            }
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


# ---------------------------------------------------------------------------
# CLI: telic intents


def intents_for(target: str, paths: list[str], root: str) -> list[dict[str, Any]]:
    """What governs a file or directory: intents declared in the intents.md
    files above or inside it, in its code, cited by its code, or naming its
    functions in by:. Loads
    and lowers only; nothing is proved."""
    from .checker import load_modules
    from .frontend.intents_md import LANGUAGE, scope_of

    rel = os.path.relpath(os.path.abspath(target), root).replace(os.sep, "/")
    rel = "" if rel == "." else rel
    mods = load_modules(paths, root)
    mine = [m for m in mods if m.language != LANGUAGE and (m.path == rel or _within(m.path, rel))]
    if not mine:
        more = load_modules([target], root)
        mine = [m for m in more if m.language != LANGUAGE]
        mods += more
    decls: dict[str, tuple[str, list[str], str]] = {}
    for m in mods:
        for d in m.intents:
            decls.setdefault(d.id, (*split_by(d.text), f"{m.path}:{d.loc.line}"))
    why: dict[str, list[str]] = {}
    for m in mods:
        if m.language == LANGUAGE and (scope_of(m.path) == rel or _within(rel, scope_of(m.path)) or _within(scope_of(m.path), rel)):
            for d in m.intents:
                why.setdefault(d.id, []).append(f"declared in {m.path}")
    for m in mine:
        for d in m.intents:
            why.setdefault(d.id, []).append(f"declared in {m.path}")
        for fn in m.functions.values():
            key = f"{m.path}::{fn.name}"
            for i in fn.intents:
                why.setdefault(i, []).append(f"cited by {fn.name}")
            for iid, (_, by, _) in decls.items():
                if any(_match(item, key, fn.name) for item in by):
                    why.setdefault(iid, []).append(f"by: lists {fn.name}")
    out = []
    for iid in sorted(why):
        text, by, at = decls.get(iid, (None, [], None))
        out.append({"id": iid, "text": text, "at": at, "by": by, "why": list(dict.fromkeys(why[iid]))})
    return out


def cmd_intents_for(args: Any) -> int:
    from .render import Paint

    root = os.path.abspath(args.root or os.getcwd())
    got = intents_for(args.for_path, args.paths, root)
    if args.json:
        print(json.dumps(got, indent=2))
        return 0
    p = Paint(None)
    if not got:
        print(p.dim(f"no intent governs {args.for_path}"))
    for x in got:
        print(f"{p.bold(p.cyan(x['id']))}  {p.dim(x['at'] or 'cited, never declared')}  {p.dim('(' + '; '.join(x['why']) + ')')}")
        if x["text"]:
            print(f"  {x['text']}")
        if x["by"]:
            print(p.dim(f"  by: {', '.join(x['by'])}"))
    return 0


def cmd_intents(args: Any, options: Any) -> int:
    from .checker import check
    from .render import Paint, Renderer

    if args.for_path:
        return cmd_intents_for(args)
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
        notes = judge(root, rep.intents, oracle=args.oracle)
    if args.json:
        print(json.dumps([_intent_json(r) for r in rep.intents], indent=2))
    else:
        paint = Paint(None)
        print("\n".join(Renderer(rep, paint).intent_table()))
        for n in _file_problems(rep):
            print(paint.yellow("  " + n))
        for n in notes:
            print(paint.dim("  " + n))
    bad = [r for r in rep.intents if r.status in ("broken", "vacuous", "undeclared") or r.pointers or (r.status == "unbacked" and r.scope is not None)]
    return 1 if bad or _file_problems(rep) else 0


def link_problems(rep: Any) -> list[tuple[str, str]]:
    """(message, file) for every broken link, scope breach, duplicate
    declaration, intents.md orphan and malformed intents.md in the report."""
    from .frontend.intents_md import LANGUAGE

    out = []
    for r in rep.intents:
        home = r.loc[0] if r.loc else next((x.path for x in r.lemmas), "")
        out += [(f"intent {r.id}: {msg}", home) for msg in r.pointers]
        if r.status == "unbacked" and r.scope is not None:
            out.append((f"intent {r.id} is declared in {home} and nothing backs it: cite it from the code, or remove it", home))
    out += [(f"{m.path}:{loc.line}: {msg}", m.path) for m in rep.modules if m.language == LANGUAGE for msg, loc in m.problems]
    return out


def _file_problems(rep: Any) -> list[str]:
    from .frontend.intents_md import LANGUAGE

    return [f"{m.path}:{loc.line}: {msg}" for m in rep.modules if m.language == LANGUAGE for msg, loc in m.problems]


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
        "scope": r.scope,
        "advice": r.advice,
        "coverage": r.coverage,
        "digest": r.digest,
    }


def add_commands(sub: Any, common: Any, options: Any) -> None:
    i = sub.add_parser("intents", help="requirements, the lemmas backing them, and whether their links hold")
    common(i)
    i.add_argument("--judge", action="store_true", help="ask the oracle whether each intent's lemmas cover it (cached; never proof)")
    i.add_argument("--oracle", default=None, help="oracle spec (builtin, jev, anthropic, cmd:..., http:..., py:...; default TELIC_ORACLE)")
    i.add_argument("--accept", nargs="+", metavar="ID", help="record that you reviewed these intents' lemmas and they cover the requirement")
    i.add_argument("--as", dest="who", help="reviewer name for --accept")
    i.add_argument("--for", dest="for_path", metavar="PATH", help="list the intents that govern PATH: declared in intents.md above it, cited in it, or naming its functions in by:")
    i.add_argument("--json", action="store_true")
    i.set_defaults(func=lambda a: cmd_intents(a, options))
