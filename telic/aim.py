"""Aims: top-level requirements, backed by lemmas one layer below.

An aim is a requirement a reviewer can read, one EARS sentence:

    #@ aim REFUND-CAP: WHEN a refund is issued, the system shall never
    #@   refund more than was paid, net of earlier refunds.
    #@   by: refund, Ledger.apply, web/checkout.ts::refundButton

It is not a formula and telic never calls it "proved". What telic proves
are lemmas: contract clauses on functions anywhere in the project (either
language) that cite the aim -- ``#@ aim REFUND-CAP`` above a function
tags its clauses, ``#@ [REFUND-CAP] ensures ...`` tags one. The ``by:`` list
points down from the aim to its lemmas; citations point back up. Both
directions are checked, so neither side can drift silently.

An aim's status says what its lemmas establish:

    backed    every lemma is proved (and so is everything they rest on)
    broken    a lemma is refuted: the code contradicts part of the requirement
    partial   some lemma is open or its function is not checkable
    vacuous-risk  a safety aim ("never X", "shall not") whose lemmas are all
              met by a stub that returns at once or raises: nothing says
              the code still does its job
    unbacked  declared, but no lemma cites it
    undeclared cited, but never declared

Whether the lemmas *cover* the requirement is a separate question that no
prover answers. It is recorded separately, as a human review (pinned to the
exact aim text and lemma set, so it goes stale when either changes) or as
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
    """Shape problems of an aim sentence against the EARS patterns
    (ubiquitous, WHEN, WHILE, IF/THEN, WHERE and their combinations). A lint,
    not a parser: it keeps requirements in one reviewable form."""
    t = " ".join(text.split())
    low = t.lower()
    out: list[str] = []
    shalls = len(re.findall(r"\bshall\b", low))
    if shalls == 0:
        out.append("has no 'shall': state the required response ('the <system> shall ...')")
    elif shalls > 1:
        out.append("has more than one 'shall': split it into one aim per requirement")
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
    kind: str  # ensures | raises | invariant | mirror | ui
    text: str
    status: str  # proved | refuted | open | trusted | unsupported | vacuous
    detail: str = ""  # for a ui lemma: what the verdict rests on


@dataclass
class AimReport:
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
    scope: str | None = None  # declared in <scope>/aims/<ID>.md ('' = the root); None = a comment
    advice: list[str] = field(default_factory=list)  # findings that do not fail
    assumes: list[str] = field(default_factory=list)  # unproved code a lemma's proof rests on
    stubs: list[str] = field(default_factory=list)  # trivial implementations its lemmas accept
    trusted: list[str] = field(default_factory=list)  # trusted functions the lemmas rest on

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


def _ui_match(item: str, lemma: Any) -> bool:
    """Does a ``by:`` item name this ui lemma? ``name``, ``ui:name`` or
    ``path::name``."""
    n = item.removeprefix("ui:")
    return _match(n, f"{lemma.path}::{lemma.name}", lemma.name)


def build(rep: Any) -> list[AimReport]:
    from .frontend.aim_file import LANGUAGE, scope_of

    decls: dict[str, tuple[str, tuple[str, int], list[str], str | None, bool]] = {}
    twice: dict[str, list[str]] = {}
    for m in sorted(rep.modules, key=lambda m: m.language == LANGUAGE and m.context):
        scope = scope_of(m.path) if m.language == LANGUAGE else None
        for d in m.aims:
            text, by = split_by(d.text)
            if d.id in decls:
                twice.setdefault(d.id, []).append(f"{m.path}:{d.loc.line}")
            else:
                decls[d.id] = (text, (m.path, d.loc.line), by, scope, m.context)
    citing: dict[str, list[Any]] = {}
    for f in rep.functions:
        for i in f.fn.aims:
            citing.setdefault(i, []).append(f)
    mirrors: dict[str, list[Any]] = {}
    for mr in rep.mirrors:
        for i in mr.aims:
            mirrors.setdefault(i, []).append(mr)
    ui = getattr(rep, "ui", None)
    uis: dict[str, list[Any]] = {}
    if ui is not None:
        for d in ui.decls:
            text, by = split_by(d.text)
            if d.id in decls:
                twice.setdefault(d.id, []).append(f"{d.path}:{d.line}")
            else:
                decls[d.id] = (text, (d.path, d.line), by, None, False)
        for res in ui.results:
            for i in res.lemma.aims:
                uis.setdefault(i, []).append(res)
    ui_lemmas = [res.lemma for rs in uis.values() for res in rs]
    lcs: dict[str, list[Any]] = {}
    for lr in getattr(rep, "lifecycles", []):
        for i in lr.aims:
            lcs.setdefault(i, []).append(lr)
    lc_classes = {lr.cls for lr in getattr(rep, "lifecycles", [])}
    reviews = _load_reviews(getattr(rep, "root", None))
    out: list[AimReport] = []
    shown = {k for k, d in decls.items() if not d[4]} | set(citing) | set(mirrors) | set(uis) | set(lcs)
    for iid in sorted(shown):
        text, loc, by, scope, context = decls.get(iid, (None, None, [], None, False))
        fns = citing.get(iid, [])
        r = AimReport(iid, text, loc, [f.ref.key for f in fns], "partial", by=by, scope=scope)
        if iid in twice and loc is not None:
            r.pointers.append(f"{iid} is declared more than once ({loc[0]}:{loc[1]}, {', '.join(twice[iid])}): keep one declaration")
        for f in fns:
            clauses = [c for c in f.fn.ensures + f.fn.raises if iid in c.aims]
            for s in _loop_invariants(f.fn):
                if iid in s.aims:
                    clauses.append(s)
            if not clauses and not any(f.ref.key in (mr.a.key, mr.b.key) for mr in mirrors.get(iid, [])):
                r.pointers.append(f"{f.fn.name} cites {iid} but none of its @ensures or @mirrors carries it")
            for c in clauses:
                r.lemmas.append(Lemma(f.ref.key, f.fn.name, f.ref.module.path, c.loc.line, c.kind, c.text, _clause_status(f, c)))
        for mr in mirrors.get(iid, []):
            st = {"proved": "proved", "refuted": "refuted", "vacuous": "vacuous"}.get(mr.status, "open")
            r.lemmas.append(Lemma(mr.a.key, f"{mr.a.fn.name} ≡ {mr.b.fn.name}", mr.a.module.path, mr.a.fn.loc.line, "mirror", "agree on every input", st))
        for res in uis.get(iid, []):
            r.lemmas.append(_ui_lemma(rep, res, r))
        for lr in lcs.get(iid, []):
            detail = "; ".join(dict.fromkeys(lr.problems))
            r.lemmas.append(Lemma(f"{lr.module.path}::{lr.cls}", _src(lr.cls), lr.module.path, lr.clause.loc.line, "lifecycle", lr.clause.text, lr.status, detail))
        # Two-sided pointers.
        if by:
            for item in by:
                hit = [f for f in rep.functions if _match(item, f.ref.key, f.fn.name)]
                classes = [c for c in lc_classes if _match(item, f"{rep.program.class_module[c].path}::{c}", _src(c))]
                if classes and not hit:
                    if not any(_match(item, f"{lr.module.path}::{lr.cls}", _src(lr.cls)) for lr in lcs.get(iid, [])):
                        r.pointers.append(f"'{item}' is listed in by: but none of its lifecycles cites {iid}")
                elif any(_ui_match(item, lm) for lm in ui_lemmas):
                    if not any(_ui_match(item, res.lemma) for res in uis.get(iid, [])):
                        r.pointers.append(f"'{item}' is listed in by: but that ui lemma does not cite {iid}")
                elif not hit:
                    path = item.split("::")[0] if "::" in item else None
                    checked = {m.path for m in rep.modules}
                    if not context or (path is not None and path in checked):
                        r.pointers.append(f"'{item}' is listed in by: but no checked function has that name")
                    elif path is not None and not os.path.exists(os.path.join(getattr(rep, "root", None) or ".", path)):
                        r.pointers.append(f"'{item}' is listed in by: but {path} does not exist")
                    elif path is not None:  # an ancestor's aim file may list code outside this check
                        r.advice.append(f"'{item}' is outside this check: 'telic check' the whole project to see it")
                elif not any(iid in f.fn.aims for f in hit):
                    r.pointers.append(f"'{item}' is listed in by: but does not cite {iid}")
            for f in fns:
                if not any(_match(item, f.ref.key, f.fn.name) for item in by):
                    r.pointers.append(f"{f.fn.name} cites {iid} but is not in its by: list")
            for lr in lcs.get(iid, []):
                if not any(_match(item, f"{lr.module.path}::{lr.cls}", _src(lr.cls)) for item in by):
                    r.pointers.append(f"the lifecycle of {_src(lr.cls)} cites {iid} but {_src(lr.cls)} is not in its by: list")
            for res in uis.get(iid, []):
                if not any(_ui_match(item, res.lemma) for item in by):
                    r.pointers.append(f"ui {res.lemma.name} cites {iid} but is not in its by: list")
        if scope is not None:
            _check_scope(r, [f.ref.module.path for item in by for f in rep.functions if _match(item, f.ref.key, f.fn.name)], partial=context, root=getattr(rep, "root", None) or ".")
        if text is not None:
            r.ears = ears_problems(text)
        status_of = {f.ref.key: f.status for f in rep.functions}
        for f in fns:
            for d in sorted(f.open_deps):
                r.assumes.append(f"{f.fn.name} assumes {d.split('::')[-1]} ({status_of.get(d, 'not checked')})")
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
            if all(x.status in ("proved", "trusted") for x in r.lemmas):
                why = [f"{f.fn.name} ({f.status})" for f in fns if f.status not in ("proved", "trusted")] + [f"{m.a.fn.name} ≡ {m.b.fn.name} ({m.status})" for m in mirrors.get(iid, []) if m.status != "proved"]
                if why:
                    r.advice.append(f"every lemma is proved, but not everything the backing functions do: {', '.join(why)}")
        r.trusted = sorted({f.fn.name for f in fns if f.status == "trusted"} | {d.split("::")[-1] for f in fns for d in f.trusted_deps})
        r.digest = digest(r)
        rv = reviews.get(iid)
        if rv is not None:
            r.coverage = {"kind": "reviewed", "by": rv.get("by", ""), "fresh": rv.get("digest") == r.digest}
        out.append(r)
    return out


_SAFETY = re.compile(r"\b(never|shall not|must not|at no time)\b", re.I)


def is_safety(text: str) -> bool:
    """A prohibition: 'never X', 'shall not X'."""
    return bool(_SAFETY.search(text))


def flag_vacuous_risk(rep: Any, opts: Any) -> None:
    """A backed safety aim is ``vacuous-risk`` when, for every function its
    lemmas sit on, a stub (return a default at once, or raise) meets that
    function's whole contract: an empty implementation would satisfy the
    aim. A lemma that says what the function still does (liveness) rules the
    stub out, and so does a mirror or a ui lemma."""
    import dataclasses

    from .gaps import trivially_met

    by_key = {f.ref.key: f for f in rep.functions}
    quiet = dataclasses.replace(opts, replay=False, lean=False, receipts=False, progress=None, only=None, ui=False)
    seen: dict[str, str | None] = {}
    for r in rep.aims:
        if r.status != "backed" or not r.text or not is_safety(r.text):
            continue
        if any(x.kind in ("mirror", "ui") for x in r.lemmas):
            continue
        stubs = []
        for key in dict.fromkeys(x.func for x in r.lemmas):
            f = by_key.get(key)
            if f is None:
                break
            if key not in seen:
                seen[key] = trivially_met(f.fn, f.ref.module, rep.modules, rep.root or ".", quiet)
            if seen[key] is None:
                break
            stubs.append(f"{f.fn.name}: `{seen[key]}` meets every lemma")
        else:
            if stubs:
                r.status = "vacuous-risk"
                r.stubs = stubs


def _src(name: str) -> str:
    from .ir import source_name

    return source_name(name)


def _within(path: str, scope: str) -> bool:
    return not scope or path.replace(os.sep, "/").startswith(scope + "/")


def _inside(root: str, path: str, scope: str) -> bool:
    """Whether the file really lives under scope, through any symlinks."""
    real = os.path.realpath(os.path.join(root, scope))
    return os.path.realpath(os.path.join(root, path)).startswith(real + os.sep)


def _check_scope(r: AimReport, targets: list[str], partial: bool, root: str) -> None:
    """A file-declared aim may only rest on code under its directory, and
    one whose lemmas all sit in one file belongs in that file (judged only
    when the check saw all of its code)."""
    scope = r.scope or ""
    outside = sorted({p for p in {x.path for x in r.lemmas} | set(targets) if not _inside(root, p, scope)})
    for path in outside:
        r.pointers.append(f"{path} is outside {scope or '.'}/, the scope of {r.loc[0] if r.loc else r.id}: move {r.id}.md to the aims/ of a directory containing both")
    files = {x.path for x in r.lemmas}
    if len(files) == 1 and not partial and not outside and set(targets) <= files:
        (only,) = files
        r.advice.append(f"every lemma is in {only}: declare {r.id} there as an '@aim {r.id}: ...' comment")


_RANK = {"refuted": 0, "open": 1, "unsupported": 1, "vacuous": 2, "trusted": 3, "proved": 4}


def _ui_lemma(rep: Any, res: Any, r: AimReport) -> Lemma:
    """A ui lemma; with 'via F', F's own verdict counts too (the control is
    reachable, and the handler behind it does what its contract says)."""
    lem = res.lemma
    status, detail = res.status, res.detail
    if res.method and status != "open":
        detail = f"{res.method}: {detail}"
    if lem.via:
        hit = [f for f in rep.functions if _match(lem.via, f.ref.key, f.fn.name)]
        if not hit:
            r.pointers.append(f"ui {lem.name}: 'via {lem.via}' names no checked function")
            status = min(status, "open", key=lambda s: _RANK.get(s, 1))
        else:
            fs = hit[0].status if not hit[0].open_deps or hit[0].status != "proved" else "open"
            fs = {"proved": "proved", "trusted": "trusted", "refuted": "refuted"}.get(fs, "open")
            detail += f"; handler {hit[0].fn.name} {fs}"
            status = min(status, fs, key=lambda s: _RANK.get(s, 1))
    return Lemma(f"ui:{lem.name}", lem.name, lem.path, lem.line, "ui", lem.text, status, detail)


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


def digest(r: AimReport) -> str:
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


def accept(root: str, r: AimReport, who: str) -> None:
    """Record that a person reviewed this aim's lemmas and found they
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


def coverage_request(r: AimReport) -> tuple[dict[str, Any], dict[str, Any]]:
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


def judge(root: str, reports: list[AimReport], oracle: str | None = None) -> list[str]:
    """Ask the oracle whether each aim's lemmas cover it. Returns messages
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
                "parts": [_part(c, got.answers.get(k)) for k, c in parts.items()],
            }
        j = cache[key]
        if r.coverage is None or r.coverage.get("kind") != "reviewed" or not r.coverage.get("fresh"):
            r.coverage = {"kind": "judged", **j}
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w") as fh:
        json.dump(cache, fh, indent=2, sort_keys=True)
    return notes


def _part(condition: str, a: dict[str, Any] | None) -> dict[str, Any]:
    from . import oracle as oracles

    p = oracles.noul(a)
    return {"condition": condition, "p": None if p is None else round(p, 2), "by": (a or {}).get("by")}


def attach_cached_judgments(root: str, reports: list[AimReport]) -> None:
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
# CLI: telic aims


def aims_for(target: str, paths: list[str], root: str) -> list[dict[str, Any]]:
    """What governs a file or directory: aims declared in the aims/
    directories above or inside it, in its code, cited by its code, or naming its
    functions in by:. Loads
    and lowers only; nothing is proved."""
    from .checker import load_modules
    from .frontend.aim_file import LANGUAGE, scope_of

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
        for d in m.aims:
            decls.setdefault(d.id, (*split_by(d.text), f"{m.path}:{d.loc.line}"))
    why: dict[str, list[str]] = {}
    for m in mods:
        if m.language == LANGUAGE and (scope_of(m.path) == rel or _within(rel, scope_of(m.path)) or _within(scope_of(m.path), rel)):
            for d in m.aims:
                why.setdefault(d.id, []).append(f"declared in {m.path}")
    for m in mine:
        for d in m.aims:
            why.setdefault(d.id, []).append(f"declared in {m.path}")
        for fn in m.functions.values():
            key = f"{m.path}::{fn.name}"
            for i in fn.aims:
                why.setdefault(i, []).append(f"cited by {fn.name}")
            for iid, (_, by, _) in decls.items():
                if any(_match(item, key, fn.name) for item in by):
                    why.setdefault(iid, []).append(f"by: lists {fn.name}")
    out = []
    for iid in sorted(why):
        text, by, at = decls.get(iid, (None, [], None))
        out.append({"id": iid, "text": text, "at": at, "by": by, "why": list(dict.fromkeys(why[iid]))})
    return out


def cmd_aims_for(args: Any) -> int:
    from .render import Paint

    root = os.path.abspath(args.root or os.getcwd())
    got = aims_for(args.for_path, args.paths, root)
    if args.json:
        print(json.dumps(got, indent=2))
        return 0
    p = Paint(None)
    if not got:
        print(p.dim(f"no aim governs {args.for_path}"))
    for x in got:
        print(f"{p.bold(p.cyan(x['id']))}  {p.dim(x['at'] or 'cited, never declared')}  {p.dim('(' + '; '.join(x['why']) + ')')}")
        if x["text"]:
            print(f"  {x['text']}")
        if x["by"]:
            print(p.dim(f"  by: {', '.join(x['by'])}"))
    return 0


def cmd_aims(args: Any, options: Any) -> int:
    from .checker import check
    from .render import Paint, Renderer

    if args.for_path:
        return cmd_aims_for(args)
    root = os.path.abspath(args.root or os.getcwd())
    rep = check(args.paths, options(args, root), root=root)
    notes: list[str] = []
    if args.accept:
        who = args.who or os.environ.get("USER") or "reviewer"
        for iid in args.accept:
            r = next((x for x in rep.aims if x.id == iid), None)
            if r is None:
                print(f"telic: no aim {iid}")
                return 2
            if r.status != "backed":
                why = f" ({'; '.join(r.stubs)}: add a lemma that says what it still does)" if r.stubs else ""
                print(f"telic: {iid} is {r.status}{why}; only a backed aim's coverage can be reviewed")
                return 1
            accept(root, r, who)
            r.coverage = {"kind": "reviewed", "by": who, "fresh": True}
            print(f"reviewed {iid} ({len(r.lemmas)} lemmas, digest {r.digest}) -> {REVIEWS}")
    if args.judge:
        notes = judge(root, rep.aims, oracle=args.oracle)
    if args.json:
        print(json.dumps([_aim_json(r) for r in rep.aims], indent=2))
    else:
        paint = Paint(None)
        print("\n".join(Renderer(rep, paint).aim_table()))
        for n in _file_problems(rep):
            print(paint.yellow("  " + n))
        for n in notes:
            print(paint.dim("  " + n))
    bad = [r for r in rep.aims if r.status in ("broken", "vacuous", "undeclared") or r.pointers or (r.status == "unbacked" and r.scope is not None)]
    return 1 if bad or _file_problems(rep) else 0


def link_problems(rep: Any) -> list[tuple[str, str]]:
    """(message, file) for every broken link, scope breach, duplicate
    declaration, orphaned aim file and malformed aim file in the report."""
    from .frontend.aim_file import LANGUAGE

    out = []
    for r in rep.aims:
        home = r.loc[0] if r.loc else next((x.path for x in r.lemmas), "")
        out += [(f"aim {r.id}: {msg}", home) for msg in r.pointers]
        if r.status == "unbacked" and r.scope is not None:
            out.append((f"aim {r.id} is declared in {home} and nothing backs it: cite it from the code, or remove it", home))
    out += [(f"{m.path}:{loc.line}: {msg}", m.path) for m in rep.modules if m.language == LANGUAGE for msg, loc in m.problems]
    return out


def _file_problems(rep: Any) -> list[str]:
    from .frontend.aim_file import LANGUAGE

    return [f"{m.path}:{loc.line}: {msg}" for m in rep.modules if m.language == LANGUAGE for msg, loc in m.problems]


def _aim_json(r: AimReport) -> dict[str, Any]:
    return {
        "id": r.id,
        "text": r.text,
        "status": r.status,
        "at": f"{r.loc[0]}:{r.loc[1]}" if r.loc else None,
        "by": r.by,
        "lemmas": [{"function": x.name, "at": f"{x.path}:{x.line}", "kind": x.kind, "text": x.text, "status": x.status, **({"detail": x.detail} if x.detail else {})} for x in r.lemmas],
        "links": r.pointers,
        "ears": r.ears,
        "scope": r.scope,
        "advice": r.advice,
        "stubs": r.stubs,
        "trusted": r.trusted,
        "coverage": r.coverage,
        "digest": r.digest,
    }


def add_commands(sub: Any, common: Any, options: Any) -> None:
    i = sub.add_parser("aims", help="requirements, the lemmas backing them, and whether their links hold")
    common(i)
    i.add_argument("--judge", action="store_true", help="ask the oracle whether each aim's lemmas cover it (cached; never proof)")
    i.add_argument("--oracle", default=None, help="oracle spec (builtin, jev, anthropic, cmd:..., http:..., py:...; default TELIC_ORACLE)")
    i.add_argument("--accept", nargs="+", metavar="ID", help="record that you reviewed these aims' lemmas and they cover the requirement")
    i.add_argument("--as", dest="who", help="reviewer name for --accept")
    i.add_argument("--for", dest="for_path", metavar="PATH", help="list the aims that govern PATH: declared in aims/ above it, cited in it, or naming its functions in by:")
    i.add_argument("--json", action="store_true")
    i.set_defaults(func=lambda a: cmd_aims(a, options))
