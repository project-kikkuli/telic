"""UI lemmas: what the running app must do, observed through its accessibility tree.

A UI lemma is a contract line with the ``ui`` keyword, written in a comment
in any file of the app (``//@``, ``#@``, ``--@`` or ``<!--@ ... -->``) and
tagged with the aims it backs:

    //@ [ESCAPE] ui escape: always reachable home from overlay
    //@ [SETTINGS] ui dark-mode: persists checkbox "Dark mode"
    //@ [NAV] ui menu-visible: unobscured button "Menu"

Properties (``P`` and ``Q`` are predicates over one screen):

    always reachable P [from Q]   from every reachable state (where Q holds), P can be reached
    reachable P                   some reachable state satisfies P
    always P [while Q]            every reachable state (where Q holds) satisfies P
    never P [while Q]             no reachable state (where Q holds) satisfies P
    unobscured T [while Q]        wherever T renders, its center and corners are not covered
    persists T                    a change to control T survives reopening the app

and any of them may end with ``via FUNC``: the handler that performs the
change, whose proof then counts toward the lemma.

Predicates: ``home`` (the start screen with nothing open), ``overlay`` or
``overlay "Name"`` (a dialog, alert or menu is open), ``screen "/path/*"``,
a target ``ROLE "name"`` (present), ``T is enabled|disabled|checked|
unchecked|expanded|collapsed|selected|pressed``, ``T == "value"``, combined
with ``not``, ``and``, ``or`` and parentheses. A name is a string (exact) or
``/regex/``; a role alone matches any name.
"""

from __future__ import annotations

import fnmatch
import json
import os
import re
from dataclasses import dataclass, field
from pathlib import Path

from ..contracts import AIM_ID, KEYWORDS
from .tree import OVERLAYS, Node, Snapshot, value_of

# ---------------------------------------------------------------------------
# Targets and predicates


@dataclass(frozen=True)
class Target:
    role: str
    name: str | None = None  # exact, whitespace-normalised
    pattern: str | None = None  # /regex/

    def matches(self, n: Node) -> bool:
        if n.role != self.role and not (self.role == "clickable" and n.pointer):
            return False
        name = " ".join((n.name or (n.text() if n.pointer else "")).split())
        if self.pattern is not None:
            return re.search(self.pattern, name) is not None
        return self.name is None or name == self.name

    def find(self, snap: Snapshot) -> list[Node]:
        return [n for n in snap.nodes() if self.matches(n)]

    def __str__(self) -> str:
        if self.pattern is not None:
            return f"{self.role} /{self.pattern}/"
        return f"{self.role} {json.dumps(self.name, ensure_ascii=False)}" if self.name is not None else self.role


_STATE_TEST = {
    "enabled": lambda n: "disabled" not in n.states,
    "disabled": lambda n: "disabled" in n.states,
    "checked": lambda n: "checked" in n.states,
    "unchecked": lambda n: "checked" not in n.states and "mixed" not in n.states,
    "expanded": lambda n: "expanded" in n.states,
    "collapsed": lambda n: "expanded" not in n.states,
    "selected": lambda n: "selected" in n.states,
    "pressed": lambda n: "pressed" in n.states,
}


@dataclass(frozen=True)
class Pred:
    op: str  # home | overlay | screen | present | is | eq | not | and | or | true
    args: tuple = ()

    def eval(self, snap: Snapshot, home: str) -> bool:
        op, a = self.op, self.args
        if op == "true":
            return True
        if op == "home":
            return snap.screen == home and not snap.overlays()
        if op == "overlay":
            ns = [n for n in snap.nodes() if n.role in OVERLAYS]
            return any(_name_ok(a[0], n.name) for n in ns) if a else bool(ns)
        if op == "screen":
            return fnmatch.fnmatchcase(snap.screen, a[0])
        if op == "present":
            return bool(a[0].find(snap))
        if op == "is":
            return any(_STATE_TEST[a[1]](n) for n in a[0].find(snap))
        if op == "eq":
            return any(value_of(n) == a[1] for n in a[0].find(snap))
        if op == "not":
            return not a[0].eval(snap, home)
        if op == "and":
            return all(x.eval(snap, home) for x in a)
        if op == "or":
            return any(x.eval(snap, home) for x in a)
        raise ValueError(op)

    def __str__(self) -> str:
        op, a = self.op, self.args
        if op in ("home", "true"):
            return op
        if op == "overlay":
            return "overlay" + (" " + str(a[0]).split(" ", 1)[1] if a and " " in str(a[0]) else "")
        if op == "screen":
            return f"screen {json.dumps(a[0])}"
        if op == "present":
            return str(a[0])
        if op == "is":
            return f"{a[0]} is {a[1]}"
        if op == "eq":
            return f"{a[0]} == {json.dumps(a[1], ensure_ascii=False)}"
        if op == "not":
            return f"not {_paren(a[0])}"
        return f" {op} ".join(_paren(x) for x in a)


def _paren(p: Pred) -> str:
    return f"({p})" if p.op in ("and", "or") else str(p)


def _name_ok(t: Target, name: str) -> bool:
    if t.pattern is not None:
        return re.search(t.pattern, name) is not None
    return t.name is None or " ".join(name.split()) == t.name


TRUE = Pred("true")


@dataclass(frozen=True)
class Prop:
    kind: str  # always_reachable | reachable | always | never | unobscured | persists
    goal: Pred | Target
    cond: Pred = TRUE

    def atoms(self) -> list[Pred]:
        """Predicates the state abstraction must keep apart for this property."""
        if self.kind in ("unobscured", "persists"):
            t = self.goal
            assert isinstance(t, Target)
            return [Pred("is", (t, "enabled"))] + ([self.cond] if self.cond is not TRUE else [])
        out = [self.goal] if isinstance(self.goal, Pred) else []
        return out + ([self.cond] if self.cond is not TRUE else [])

    def __str__(self) -> str:
        head = {"always_reachable": "always reachable", "reachable": "reachable", "always": "always", "never": "never", "unobscured": "unobscured", "persists": "persists"}[self.kind]
        tail = ""
        if self.cond is not TRUE:
            tail = (" from " if self.kind == "always_reachable" else " while ") + str(self.cond)
        return f"{head} {self.goal}{tail}"


# ---------------------------------------------------------------------------
# Parsing


class SpecError(Exception):
    pass


_TOKEN = re.compile(r'\s*(?:(?P<str>"(?:[^"\\]|\\.)*")|(?P<re>/(?:[^/\\]|\\.)+/i?)|(?P<op>==|[()])|(?P<word>[A-Za-z_][\w.:/-]*))')
_ROLE = re.compile(r"^[a-z][a-z]*$")


def _tokens(text: str) -> list[tuple[str, str]]:
    out: list[tuple[str, str]] = []
    pos = 0
    text = text.rstrip()
    while pos < len(text):
        m = _TOKEN.match(text, pos)
        if not m or m.end() == pos:
            raise SpecError(f"cannot read {text[pos:].strip()[:30]!r}")
        kind = m.lastgroup or ""
        out.append((kind, m.group(kind)))
        pos = m.end()
    return out


class _Parser:
    def __init__(self, text: str):
        self.toks = _tokens(text)
        self.i = 0

    def peek(self, k: int = 0) -> tuple[str, str] | None:
        return self.toks[self.i + k] if self.i + k < len(self.toks) else None

    def word(self, *ws: str) -> bool:
        t = self.peek()
        if t and t[0] == "word" and t[1] in ws:
            self.i += 1
            return True
        return False

    def need(self, what: str) -> tuple[str, str]:
        t = self.peek()
        if t is None:
            raise SpecError(f"expected {what} at the end")
        self.i += 1
        return t

    def prop(self) -> tuple[Prop, str | None]:
        if self.word("always"):
            if self.word("reachable"):
                goal = self.pred()
                cond = self.pred() if self.word("from") else TRUE
                p = Prop("always_reachable", goal, cond)
            else:
                goal = self.pred()
                p = Prop("always", goal, self.pred() if self.word("while") else TRUE)
        elif self.word("reachable"):
            p = Prop("reachable", self.pred())
        elif self.word("never"):
            goal = self.pred()
            p = Prop("never", goal, self.pred() if self.word("while") else TRUE)
        elif self.word("unobscured"):
            t = self.target()
            p = Prop("unobscured", t, self.pred() if self.word("while") else TRUE)
        elif self.word("persists"):
            p = Prop("persists", self.target())
        else:
            t = self.peek()
            raise SpecError(f"expected 'always reachable', 'reachable', 'always', 'never', 'unobscured' or 'persists', got {t[1] if t else 'nothing'!r}")
        via = None
        if self.word("via"):
            k, v = self.need("a function name after 'via'")
            if k != "word":
                raise SpecError("'via' takes a function name")
            via = v
        if self.peek() is not None:
            raise SpecError(f"unexpected {self.peek()[1]!r}")
        return p, via

    def pred(self) -> Pred:
        left = self.conj()
        parts = [left]
        while self.word("or"):
            parts.append(self.conj())
        return parts[0] if len(parts) == 1 else Pred("or", tuple(parts))

    def conj(self) -> Pred:
        parts = [self.unary()]
        while self.word("and"):
            parts.append(self.unary())
        return parts[0] if len(parts) == 1 else Pred("and", tuple(parts))

    def unary(self) -> Pred:
        if self.word("not"):
            return Pred("not", (self.unary(),))
        t = self.peek()
        if t == ("op", "("):
            self.i += 1
            p = self.pred()
            if self.need("')'") != ("op", ")"):
                raise SpecError("expected ')'")
            return p
        if self.word("home"):
            return Pred("home")
        if self.word("overlay"):
            nt = self.peek()
            if nt and nt[0] in ("str", "re"):
                return Pred("overlay", (self._named("overlay"),))
            return Pred("overlay")
        if self.word("screen"):
            k, v = self.need("a screen after 'screen'")
            if k != "str":
                raise SpecError("'screen' takes a quoted path, e.g. screen \"/settings\"")
            return Pred("screen", (json.loads(v),))
        tgt = self.target()
        if self.word("is"):
            k, v = self.need("a state after 'is'")
            if v not in _STATE_TEST:
                raise SpecError(f"unknown state {v!r} (one of {', '.join(_STATE_TEST)})")
            return Pred("is", (tgt, v))
        if self.peek() == ("op", "=="):
            self.i += 1
            k, v = self.need("a value after '=='")
            if k != "str":
                raise SpecError("'==' compares with a quoted value")
            return Pred("eq", (tgt, json.loads(v)))
        return Pred("present", (tgt,))

    def target(self) -> Target:
        k, v = self.need("a role, e.g. button \"Close\"")
        if k != "word" or not _ROLE.match(v) or v in ("and", "or", "not", "is", "while", "from", "via"):
            raise SpecError(f"expected a role (button, link, dialog, ...), got {v!r}")
        return self._named(v)

    def _named(self, role: str) -> Target:
        t = self.peek()
        if t and t[0] == "str":
            self.i += 1
            return Target(role, " ".join(json.loads(t[1]).split()))
        if t and t[0] == "re":
            self.i += 1
            body = t[1][1:-2] if t[1].endswith("/i") else t[1][1:-1]
            return Target(role, None, ("(?i)" if t[1].endswith("/i") else "") + body)
        return Target(role)


def parse_prop(text: str) -> tuple[Prop, str | None]:
    return _Parser(text).prop()


# ---------------------------------------------------------------------------
# Finding lemmas in source


@dataclass
class UiLemma:
    name: str
    path: str  # relative to the root
    line: int
    text: str  # the property as written
    aims: tuple[str, ...]
    prop: Prop | None = None
    via: str | None = None
    problem: str | None = None


@dataclass
class UiDecl:
    """An '@aim ID: sentence' in a file no language frontend reads (a .svelte, .jsx or .html file)."""

    id: str
    text: str
    path: str
    line: int


@dataclass
class Scan:
    lemmas: list[UiLemma] = field(default_factory=list)
    aims: list[UiDecl] = field(default_factory=list)


SOURCE_EXT = (
    ".py", ".ts", ".tsx", ".mts", ".cts", ".js", ".jsx", ".mjs", ".cjs", ".svelte", ".vue", ".astro",
    ".html", ".htm", ".rs", ".swift", ".kt", ".kts", ".dart", ".java", ".m", ".cs",
)
HOST_EXT = (".py", ".ts", ".tsx", ".mts", ".cts", ".rs", ".swift")  # a language frontend reads their aims
SKIP_DIRS = {"node_modules", "__pycache__", "venv", ".venv", "dist", "build", "target", ".git", ".telic", ".svelte-kit", "coverage"}

_MARK = re.compile(r"^\s*(?:<!--|//|#|--|\*|/\*+)@\s?(?P<body>.*?)(?:\s*-->|\s*\*/)?\s*$")
_TAGS = re.compile(rf"^\[\s*({AIM_ID}(?:\s*,\s*{AIM_ID})*)\s*\]\s*")
_HEAD = re.compile(r"^(?P<name>[a-z][\w-]*)\s*:\s*(?P<prop>.*)$", re.S)
_DECL = re.compile(rf"^({AIM_ID})\s*:\s*(.*)$", re.S)


def files_under(paths: list[str]) -> list[str]:
    out: list[str] = []
    for p in paths:
        if os.path.isdir(p):
            for dirpath, dirnames, filenames in os.walk(p):
                dirnames[:] = sorted(d for d in dirnames if d not in SKIP_DIRS and not d.startswith("."))
                out += [os.path.join(dirpath, f) for f in sorted(filenames) if f.endswith(SOURCE_EXT)]
        elif p.endswith(SOURCE_EXT) and os.path.exists(p):
            out.append(p)
    return out


def scan(paths: list[str], root: str) -> Scan:
    """UI lemmas in the given files and directories, plus aims declared
    in files no frontend reads."""
    got = Scan()
    seen: set[str] = set()
    for f in files_under(paths):
        full = os.path.normpath(os.path.abspath(f))
        if full in seen:
            continue
        seen.add(full)
        try:
            src = Path(full).read_text(encoding="utf-8")
        except (OSError, UnicodeDecodeError):
            continue
        if "@" not in src:
            continue
        rel = os.path.relpath(full, root)
        scan_source(src, rel, got, host=full.endswith(HOST_EXT))
    return got


def scan_source(src: str, rel: str, got: Scan, host: bool = False) -> None:
    lines = src.splitlines()
    i = 0
    while i < len(lines):
        m = _MARK.match(lines[i])
        if not m:
            i += 1
            continue
        body = m.group("body").strip()
        tags: tuple[str, ...] = ()
        tm = _TAGS.match(body)
        if tm:
            tags = tuple(t.strip() for t in tm.group(1).split(","))
            body = body[tm.end():]
        word = body.split(None, 1)[0] if body else ""
        if word not in ("ui", "aim") or (word == "aim" and host):
            i += 1
            continue
        start = i
        payload = body[len(word):].strip()
        i += 1
        while i < len(lines):
            n = _MARK.match(lines[i])
            if not n:
                break
            nb = n.group("body").strip()
            first = nb.split(None, 1)[0] if nb else ""
            if not nb or first in KEYWORDS or first == "ui" or nb.startswith("["):
                break
            payload += " " + nb
            i += 1
        payload = " ".join(payload.split())
        if word == "aim":
            d = _DECL.match(payload)
            if d:
                got.aims.append(UiDecl(d.group(1), d.group(2).strip(), rel, start + 1))
            continue
        h = _HEAD.match(payload)
        if not h:
            got.lemmas.append(UiLemma("?", rel, start + 1, payload, tags, problem="write '@ui NAME: property', e.g. '//@ [ESCAPE] ui escape: always reachable home from overlay'"))
            continue
        lem = UiLemma(h.group("name"), rel, start + 1, h.group("prop").strip(), tags)
        try:
            lem.prop, lem.via = parse_prop(lem.text)
        except SpecError as e:
            lem.problem = f"ui {lem.name}: {e}"
        if not tags:
            lem.problem = lem.problem or f"ui {lem.name} backs no aim: tag it, e.g. '//@ [ESCAPE] ui {lem.name}: ...'"
        got.lemmas.append(lem)
