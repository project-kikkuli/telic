"""Lifecycles: how an object may change from one call to the next.

A ``lifecycle`` line in a class body is a history constraint: a relation
between an object before any call and after it. Every form is reflexive and
transitive (telic proves that too), so a relation every call keeps also holds
across any sequence of calls::

    #@ lifecycle status: PENDING -> PAID -> SHIPPED, PENDING | PAID -> CANCELLED
    #@ lifecycle never status: SHIPPED -> PENDING
    #@ lifecycle monotonic self.refunded
    #@ lifecycle once self.status == Status.DELIVERED
    #@ lifecycle implies(old(self.closed), self.closed)

This module is language-neutral: it parses the payload and writes each
relation, and the steps coverage asks about, as source text in the host
language, which the frontend lowers like any other spec.
"""

from __future__ import annotations

import re
import dataclasses
from dataclasses import dataclass

_GRAPH = re.compile(r"^(?:(?:self|this)\.)?([A-Za-z_]\w*)\s*:(?!:)\s*(.+)$", re.S)


class LifecycleError(Exception):
    pass


@dataclass
class Form:
    kind: str  # graph | never | monotonic | once | step
    field: str = ""
    edges: list[tuple[str, str]] = dataclasses.field(default_factory=list)
    expr: str = ""


@dataclass(frozen=True)
class Dialect:
    this: str
    eq: str
    and_: str
    or_: str
    not_: str


DIALECTS = {
    "python": Dialect("self", "==", "and", "or", "not "),
    "typescript": Dialect("this", "===", "&&", "||", "!"),
    "rust": Dialect("self", "==", "&&", "||", "!"),
}


def _split(text: str, sep: str) -> list[str]:
    """Split at ``sep`` outside brackets and quotes."""
    out, depth, quote, cur, i = [], 0, "", "", 0
    while i < len(text):
        ch = text[i]
        if quote:
            cur += ch
            if ch == "\\" and i + 1 < len(text):
                cur += text[i + 1]
                i += 1
            elif ch == quote:
                quote = ""
        elif ch in "\"'`":
            quote = ch
            cur += ch
        elif ch in "([{":
            depth += 1
            cur += ch
        elif ch in ")]}":
            depth -= 1
            cur += ch
        elif depth == 0 and text.startswith(sep, i) and not (sep == "|" and text.startswith("||", i)):
            out.append(cur)
            cur = ""
            i += len(sep)
            continue
        else:
            cur += ch
        i += 1
    out.append(cur)
    return [" ".join(x.split()) for x in out]


def _edges(body: str) -> list[tuple[str, str]]:
    edges: list[tuple[str, str]] = []
    for chain in _split(body, ","):
        if not chain:
            continue
        stops = [[s for s in _split(stop, "|")] for stop in _split(chain, "->")]
        if len(stops) < 2 or any(not s for stop in stops for s in stop):
            raise LifecycleError(f"'{chain}' is not a transition: write 'A -> B' (chains 'A -> B -> C' and alternatives 'A | B -> C' work too)")
        for a_set, b_set in zip(stops, stops[1:]):
            for a in a_set:
                for b in b_set:
                    if (a, b) not in edges:
                        edges.append((a, b))
    if not edges:
        raise LifecycleError("no transitions listed")
    return edges


def parse(payload: str) -> Form:
    text = " ".join(payload.split())
    if not text:
        raise LifecycleError("empty '@lifecycle'")
    word, _, rest = text.partition(" ")
    if word == "never":
        m = _GRAPH.match(rest)
        if not m:
            raise LifecycleError("write 'never FIELD: A -> B'")
        return Form("never", m.group(1), _edges(m.group(2)))
    if word in ("monotonic", "once"):
        if not rest:
            raise LifecycleError(f"'{word}' needs an expression over the object's fields")
        return Form(word, expr=rest)
    m = _GRAPH.match(text)
    if m and "->" in m.group(2):
        return Form("graph", m.group(1), _edges(m.group(2)))
    if "old(" not in text:
        raise LifecycleError("a lifecycle relates an object before a call (old(...)) to after it; or write 'FIELD: A -> B', 'never FIELD: A -> B', 'monotonic E' or 'once P'")
    return Form("step", expr=text)


def closure(edges: list[tuple[str, str]]) -> list[tuple[str, str]]:
    """Every (a, b) with a path of one or more declared steps, a != b, in a
    stable order."""
    states: list[str] = []
    for a, b in edges:
        for s in (a, b):
            if s not in states:
                states.append(s)
    succ = {s: [b for a, b in edges if a == s] for s in states}
    out: list[tuple[str, str]] = []
    for s in states:
        seen: list[str] = []
        todo = list(succ[s])
        while todo:
            t = todo.pop(0)
            if t in seen:
                continue
            seen.append(t)
            todo += succ[t]
        out += [(s, t) for t in seen if t != s]
    return out


@dataclass
class Texts:
    """What the frontend lowers: the relation, and each probe's step (and
    creation) condition, all in host syntax."""

    relation: str
    probes: list[tuple[str, str, str | None]]


def texts(form: Form, lang: str) -> Texts:
    d = DIALECTS[lang]
    par = lambda x: f"({x})"  # noqa: E731
    if form.kind in ("graph", "never"):
        s = f"{d.this}.{form.field}"
        eq = lambda a, b: f"{a} {d.eq} {b}"  # noqa: E731
        pair = lambda a, b: par(f"{eq(f'old({s})', a)} {d.and_} {eq(s, b)}")  # noqa: E731
        if form.kind == "graph":
            rel = f" {d.or_} ".join([eq(f"old({s})", s)] + [pair(a, b) for a, b in closure(form.edges)])
            return Texts(rel, [(f"{a} -> {b}", pair(a, b), None) for a, b in form.edges])
        rel = f" {d.and_} ".join(f"{d.not_}{pair(a, b)}" for a, b in form.edges)
        reached: list[tuple[str, str, str | None]] = []
        for a, _ in form.edges:
            if all(a != x for x, _, _ in reached):
                reached.append((a, par(f"{d.not_}{par(eq(f'old({s})', a))} {d.and_} {eq(s, a)}"), eq(s, a)))
        return Texts(rel, [(f"reaches {a}", st, cr) for a, st, cr in reached])
    e = form.expr
    if form.kind == "monotonic":
        return Texts(f"old({e}) <= {par(e)}", [("grows", f"old({e}) < {par(e)}", None)])
    if form.kind == "once":
        return Texts(f"{d.not_}{par(f'old({e})')} {d.or_} {par(e)}", [("becomes true", f"{d.not_}{par(f'old({e})')} {d.and_} {par(e)}", e)])
    return Texts(e, [])


def build(payload: str, loc, tags: tuple[str, ...], lang: str, lower) -> "ir.Lifecycle":
    """Parse one lifecycle line and lower its texts with ``lower(text,
    two_state)``, which returns an IR expression over ``self``."""
    from . import ir

    def own(text: str, two_state: bool) -> "ir.Expr":
        # only the object's own fields: otherwise code that never touches
        # it could change what its lifecycle says, unchecked
        e = lower(text, two_state)
        for sub in ir.walk_expr(e):
            if isinstance(sub, ir.Field) and isinstance(sub.obj.ty, ir.TClass) and not (isinstance(sub.obj, ir.Var) and sub.obj.name == "self"):
                raise LifecycleError("a lifecycle may only read fields of the object itself, not of other objects")
            if (isinstance(sub, ir.Quant) and "self" in (sub.idx, sub.elem)) or (isinstance(sub, ir.Builtin) and sub.name == "comp" and isinstance(sub.args[1], ir.Lit) and sub.args[1].value == "self"):
                raise LifecycleError("a lifecycle may not rebind 'self'")
            if isinstance(sub, ir.Call) and any(ir.reaches_object(a.ty) for a in sub.args):
                raise LifecycleError("a lifecycle may not call functions on objects (they could read other objects); write it on the object's fields")
        return e

    form = parse(payload)
    t = texts(form, lang)
    clause = ir.Clause("lifecycle", own(t.relation, True), loc, " ".join(payload.split()), tags)
    probes = tuple(ir.Probe(label, own(st, True), own(cr, False) if cr is not None else None) for label, st, cr in t.probes)
    return ir.Lifecycle(form.kind, clause, t.relation, probes)
