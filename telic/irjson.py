"""The IR as JSON, and logic terms as JSON: the interchange between the
Python front ends and the native engine (core/).

IR JSON uses the same schema the TypeScript lowering emits (decoded by
``telic.frontend.typescript``), so one decoder on the engine side serves both
languages. Terms travel as a DAG table: each entry refers to earlier entries
by index, so shared subterms are sent once.
"""

from __future__ import annotations

from fractions import Fraction
from typing import Any

from . import ir
from . import logic as L

# ---------------------------------------------------------------------------
# IR -> JSON


def ty(t: ir.Type) -> dict[str, Any]:
    if isinstance(t, ir.TInt):
        return {"k": "int"}
    if isinstance(t, ir.TReal):
        return {"k": "real"}
    if isinstance(t, ir.TBool):
        return {"k": "bool"}
    if isinstance(t, ir.TStr):
        return {"k": "str"}
    if isinstance(t, ir.TNone):
        return {"k": "none"}
    if isinstance(t, ir.TList):
        return {"k": "list", "elem": ty(t.elem)}
    if isinstance(t, ir.TRecord):
        return {"k": "record", "name": t.name, "fields": [[n, ty(f)] for n, f in t.fields]}
    if isinstance(t, ir.TOption):
        return {"k": "option", "inner": ty(t.inner)}
    if isinstance(t, ir.TDict):
        return {"k": "dict", "key": ty(t.key), "val": ty(t.val), "js": t.js or ""}
    if isinstance(t, ir.TClass):
        return {"k": "class", "name": t.name}
    if isinstance(t, ir.TOpaque):
        return {"k": "opaque", "why": t.why}
    if isinstance(t, ir.TEnum):
        return {"k": "enum", "name": t.name, "members": list(t.members), "values": [v if isinstance(v, (int, str)) else None for v in t.values]}
    raise TypeError(t)


def without_locs(x: Any) -> Any:
    if isinstance(x, dict):
        return {k: without_locs(v) for k, v in x.items() if k not in ("loc", "end_line")}
    if isinstance(x, list):
        return [without_locs(v) for v in x]
    return x


def loc(l: ir.Loc) -> list[int]:
    return [l.line, l.col, l.end_col]


def expr(e: ir.Expr) -> dict[str, Any]:
    d: dict[str, Any] = {"e": type(e).__name__, "ty": ty(e.ty), "loc": loc(e.loc)}
    if isinstance(e, ir.Lit):
        v = e.value
        if isinstance(v, Fraction):
            d["frac"] = [v.numerator, v.denominator]
            d["value"] = None
        else:
            d["value"] = v
    elif isinstance(e, ir.Var):
        d["name"] = e.name
    elif isinstance(e, ir.Old):
        d["expr"] = expr(e.expr)
    elif isinstance(e, ir.Unary):
        d.update(op=e.op, arg=expr(e.arg))
    elif isinstance(e, ir.Binary):
        d.update(op=e.op, left=expr(e.left), right=expr(e.right))
    elif isinstance(e, ir.Ite):
        d.update(cond=expr(e.cond), then=expr(e.then), orelse=expr(e.orelse))
    elif isinstance(e, ir.Call):
        d.update(func=e.func, args=[expr(a) for a in e.args])
    elif isinstance(e, ir.Builtin):
        d.update(name=e.name, args=[expr(a) for a in e.args])
    elif isinstance(e, ir.Index):
        d.update(seq=expr(e.seq), idx=expr(e.idx), wrap=e.wrap)
    elif isinstance(e, ir.Field):
        d.update(obj=expr(e.obj), name=e.name)
    elif isinstance(e, ir.Quant):
        d.update(kind=e.kind, idx=e.idx, lo=expr(e.lo), hi=expr(e.hi), body=expr(e.body), elem=e.elem, seq=expr(e.seq) if e.seq is not None else None)
    elif isinstance(e, ir.ListLit):
        d["elems"] = [expr(a) for a in e.elems]
    elif isinstance(e, ir.RecordLit):
        d["fields"] = [[n, expr(v)] for n, v in e.fields]
    elif isinstance(e, ir.New):
        d.update(cls=e.cls, args=[expr(a) for a in e.args])
    elif isinstance(e, ir.Extern):
        d.update(name=e.name, args=[expr(a) for a in e.args])
    return d


def clause(c: ir.Clause | None) -> dict[str, Any] | None:
    if c is None:
        return None
    return {"kind": c.kind, "expr": expr(c.expr), "loc": loc(c.loc), "text": c.text, "aims": list(c.aims), "inferred": bool(getattr(c, "inferred", False))}


def stmts(xs) -> list[dict[str, Any]]:
    return [stmt(s) for s in xs]


def stmt(s: ir.Stmt) -> dict[str, Any]:
    d: dict[str, Any] = {"s": type(s).__name__, "loc": loc(s.loc)}
    if isinstance(s, ir.Assign):
        d.update(name=s.name, value=expr(s.value))
    elif isinstance(s, ir.IndexAssign):
        d.update(name=s.name, idx=expr(s.idx), value=expr(s.value), wrap=s.wrap)
    elif isinstance(s, ir.Append):
        d.update(name=s.name, value=expr(s.value))
    elif isinstance(s, ir.If):
        d.update(cond=expr(s.cond), then=stmts(s.then), orelse=stmts(s.orelse))
    elif isinstance(s, ir.While):
        d.update(cond=expr(s.cond), invariants=[clause(c) for c in s.invariants], decreases=clause(s.decreases), body=stmts(s.body), step=stmts(s.step))
    elif isinstance(s, ir.ForRange):
        d.update(var=s.var, lo=expr(s.lo), hi=expr(s.hi), invariants=[clause(c) for c in s.invariants], body=stmts(s.body), reeval=s.reeval)
    elif isinstance(s, ir.ForEach):
        d.update(elem=s.elem, idx=s.idx, seq=expr(s.seq), invariants=[clause(c) for c in s.invariants], body=stmts(s.body), idx_visible=s.idx_visible)
    elif isinstance(s, ir.Return):
        d["value"] = expr(s.value) if s.value is not None else None
    elif isinstance(s, (ir.AssertStmt, ir.AssumeStmt)):
        d["clause"] = clause(s.clause)
        d["native"] = bool(getattr(s, "native", False))
    elif isinstance(s, ir.Raise):
        d.update(what=s.what, caught=s.caught)
    elif isinstance(s, ir.ExprStmt):
        d["expr"] = expr(s.expr)
    elif isinstance(s, ir.Unsupported):
        d["reason"] = s.reason
    elif isinstance(s, ir.FieldAssign):
        d.update(obj=expr(s.obj), cls=s.cls, field=s.field, value=expr(s.value))
    elif isinstance(s, ir.DictDel):
        d.update(name=s.name, key=expr(s.key), strict=s.strict)
    elif isinstance(s, ir.Try):
        d.update(body=stmts(s.body), handlers=[stmts(h) for h in s.handlers], orelse=stmts(s.orelse), finalbody=stmts(s.finalbody))
    return d


def function(f: ir.Function) -> dict[str, Any]:
    return {
        "name": f.name,
        "loc": loc(f.loc),
        "end_line": f.end_line,
        "params": [[p.name, ty(p.ty)] for p in f.params],
        "ret": ty(f.ret),
        "requires": [clause(c) for c in f.requires],
        "ensures": [clause(c) for c in f.ensures],
        "decreases": clause(f.decreases),
        "raises": [clause(c) for c in f.raises],
        "body": stmts(f.body),
        "aims": list(f.aims),
        "unsupported": [[m, l.line] for m, l in f.unsupported],
        "trusted": f.trusted,
        "locals": {n: ty(t) for n, t in f.locals.items()},
        "escaped": sorted(f.escaped),
    }


def module(m: ir.Module) -> dict[str, Any]:
    return {
        "path": m.path,
        "language": m.language,
        "functions": [function(f) for f in m.functions.values()],
        "records": {n: ty(t) for n, t in m.records.items()},
        "classes": {n: {"fields": [[f, ty(t)] for f, t in c.fields], "invariants": [clause(x) for x in c.invariants], "loc": loc(c.loc), "bases": list(c.bases), "owner": dict(c.owner)} for n, c in m.classes.items()},
        "imports": {k: list(v) for k, v in m.imports.items()},
        "context": m.context,
    }


# ---------------------------------------------------------------------------
# Terms <-> JSON (a DAG table)


class TermWriter:
    def __init__(self) -> None:
        self.sorts: list[Any] = []
        self.sort_ids: dict[L.Sort, int] = {}
        self.terms: list[Any] = []
        self.ids: dict[int, int] = {}  # id(term) -> index
        self.keep: list[L.Term] = []  # keep terms alive so id() stays unique

    def sort(self, s: L.Sort) -> int:
        if s in self.sort_ids:
            return self.sort_ids[s]
        if s.name == "Array":
            enc = ["Array", self.sort(L.index_sort(s)), self.sort(s.elem)]  # type: ignore[arg-type]
        elif s.name == "Rec":
            enc = ["Rec", s.rec, [[n, self.sort(fs)] for n, fs in s.fields]]
        else:
            enc = [s.name]
        self.sort_ids[s] = len(self.sorts)
        self.sorts.append(enc)
        return self.sort_ids[s]

    def term(self, t: L.Term) -> int:
        k = id(t)
        if k in self.ids:
            return self.ids[k]
        if isinstance(t, L.Const):
            enc: Any = ["c", t.name, self.sort(t.sort)]
        elif isinstance(t, L.IntV):
            enc = ["i", str(t.value)]
        elif isinstance(t, L.RealV):
            enc = ["r", str(t.value.numerator), str(t.value.denominator)]
        elif isinstance(t, L.BoolV):
            enc = ["b", t.value]
        elif isinstance(t, L.StrV):
            enc = ["s", t.value]
        elif isinstance(t, L.App):
            enc = ["a", t.op, self.sort(t.sort), [self.term(a) for a in t.args]]
        elif isinstance(t, L.Fn):
            enc = ["f", t.name, self.sort(t.sort), [self.term(a) for a in t.args]]
        elif isinstance(t, L.Quant):
            enc = ["q", t.kind, [self.term(v) for v in t.vars], self.term(t.body), [[self.term(x) for x in p] for p in t.patterns]]
        else:  # pragma: no cover
            raise TypeError(t)
        self.ids[k] = len(self.terms)
        self.terms.append(enc)
        self.keep.append(t)
        return self.ids[k]

    def dump(self) -> dict[str, Any]:
        return {"sorts": self.sorts, "terms": self.terms}


class TermReader:
    def __init__(self, table: dict[str, Any]) -> None:
        self.sorts: list[L.Sort] = []
        for enc in table["sorts"]:
            if enc[0] == "Array":
                self.sorts.append(L.ARRAY(self.sorts[enc[2]], self.sorts[enc[1]]))
            elif enc[0] == "Rec":
                self.sorts.append(L.REC(enc[1], tuple((n, self.sorts[i]) for n, i in enc[2])))
            else:
                self.sorts.append(L.Sort(enc[0]))
        self.terms: list[L.Term] = []
        for enc in table["terms"]:
            self.terms.append(self._build(enc))

    def _build(self, enc: list[Any]) -> L.Term:
        tag = enc[0]
        if tag == "c":
            return L.Const(enc[1], self.sorts[enc[2]])
        if tag == "i":
            return L.IntV(int(enc[1]))
        if tag == "r":
            return L.RealV(Fraction(int(enc[1]), int(enc[2])))
        if tag == "b":
            return L.BoolV(bool(enc[1]))
        if tag == "s":
            return L.StrV(enc[1])
        if tag == "a":
            return L.App(enc[1], tuple(self.terms[i] for i in enc[3]), self.sorts[enc[2]])
        if tag == "f":
            return L.Fn(enc[1], tuple(self.terms[i] for i in enc[3]), self.sorts[enc[2]])
        if tag == "q":
            return L.Quant(enc[1], tuple(self.terms[i] for i in enc[2]), self.terms[enc[3]], patterns=tuple(tuple(self.terms[i] for i in p) for p in enc[4]))  # type: ignore[arg-type]
        raise ValueError(enc)
