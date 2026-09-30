"""Render IR expressions back to readable, language-neutral source text."""

from __future__ import annotations

from . import ir

_OPS = {
    "add": ("+", 6), "sub": ("-", 6), "mul": ("*", 7), "rdiv": ("/", 7),
    "floordiv": ("//", 7), "fmod": ("%", 7), "tmod": ("%", 7),
    "lt": ("<", 4), "le": ("<=", 4), "gt": (">", 4), "ge": (">=", 4),
    "eq": ("==", 4), "ne": ("!=", 4), "and": ("and", 2), "or": ("or", 1),
    "implies": ("==>", 0),
}


def render(e: ir.Expr, prec: int = -1) -> str:
    if isinstance(e, ir.Lit):
        if isinstance(e.value, bool):
            return "True" if e.value else "False"
        return repr(e.value) if isinstance(e.value, str) else str(e.value)
    if isinstance(e, ir.Var):
        return e.name.split("$")[0]
    if isinstance(e, ir.Result):
        return "result"
    if isinstance(e, ir.Old):
        return f"old({render(e.expr)})"
    if isinstance(e, ir.Unary):
        return f"-{render(e.arg, 8)}" if e.op == "neg" else f"not {render(e.arg, 3)}"
    if isinstance(e, ir.Binary):
        sym, p = _OPS[e.op]
        s = f"{render(e.left, p)} {sym} {render(e.right, p + 1)}"
        return f"({s})" if p <= prec else s
    if isinstance(e, ir.Ite):
        return f"({render(e.then)} if {render(e.cond)} else {render(e.orelse)})"
    if isinstance(e, ir.Call):
        return f"{e.func}({', '.join(render(a) for a in e.args)})"
    if isinstance(e, ir.Builtin):
        if e.name in ("to_real", "to_opaque"):
            return render(e.args[0], prec)
        if e.name == "str_len":
            return f"len({render(e.args[0])})"
        if e.name == "slice":
            lo = "" if isinstance(e.args[1], ir.Lit) and e.args[1].value is None else render(e.args[1])
            hi = "" if isinstance(e.args[2], ir.Lit) and e.args[2].value is None else render(e.args[2])
            return f"{render(e.args[0], 9)}[{lo}:{hi}]"
        return f"{e.name}({', '.join(render(a) for a in e.args)})"
    if isinstance(e, ir.Index):
        return f"{render(e.seq, 9)}[{render(e.idx)}]"
    if isinstance(e, ir.Field):
        return f"{render(e.obj, 9)}.{e.name}"
    if isinstance(e, ir.Quant):
        f = "all" if e.kind == "forall" else "any"
        tgt = e.elem if e.seq is not None else e.idx
        src = render(e.seq) if e.seq is not None else f"range({render(e.lo)}, {render(e.hi)})"
        return f"{f}({render(e.body)} for {tgt} in {src})"
    if isinstance(e, ir.ListLit):
        return "[" + ", ".join(render(x) for x in e.elems) + "]"
    return type(e).__name__
