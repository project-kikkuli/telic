"""Lowering Swift expressions to the IR (see swift.py for the model)."""

from __future__ import annotations

import re
from fractions import Fraction
from typing import Any

from .. import ir
from .swift import INT_KINDS, LOGGING, REAL_TYPES, STR_TYPES, FnInfo, LowerError, TypeInfo, int_range
from .swift_syntax import Unsupported, X, norm, text

BINOPS = {"+": "add", "-": "sub", "*": "mul", "<": "lt", "<=": "le", ">": "gt", ">=": "ge"}
SCALARS = (ir.TInt, ir.TReal, ir.TBool, ir.TEnum)
STRING_TO_STRING = {"lowercased", "uppercased", "capitalized", "trimmingCharacters", "replacingOccurrences", "appending", "padding", "description", "debugDescription"}
INT_MAX = (1 << 63) - 1


class TypeRef:
    """A type named in an expression (``Int``, ``Shape``, ``Self``)."""

    def __init__(self, name: str, info: TypeInfo | None):
        self.name = name
        self.info = info


class ExprLowerer:
    """Lowers one expression. Statements it needs first (a call, a copy, an
    if used as a value) go to ``pre``, in evaluation order; code that must
    not run unconditionally (the right of '&&', a branch) is lowered into its
    own lowerer and guarded."""

    def __init__(self, fl: Any, spec: bool = False, line_offset: int = 0, col_offset: int = 0, allow_old: bool = False, allow_result: bool = False):
        self.fl = fl
        self.pj = fl.pj
        self.spec = spec
        self.pre: list[ir.Stmt] = []
        self.kinds: dict[int, str] = {}
        self.keep: list[ir.Expr] = []
        self.bound: dict[str, ir.Type] = {}
        self.bound_kinds: dict[str, str] = {}
        self.line_offset = line_offset
        self.col_offset = col_offset
        self.allow_old = allow_old
        self.allow_result = allow_result
        self.try_kind: str | None = None

    def sub(self) -> "ExprLowerer":
        e = ExprLowerer(self.fl, self.spec, self.line_offset, self.col_offset, self.allow_old, self.allow_result)
        e.bound = dict(self.bound)
        e.bound_kinds = dict(self.bound_kinds)
        e.kinds = self.kinds
        e.keep = self.keep
        e.try_kind = self.try_kind
        return e

    def loc(self, x: Any) -> ir.Loc:
        (l1, c1), (l2, c2) = x.start_point, x.end_point
        if self.spec:
            return ir.Loc(l1 + 1 + self.line_offset, c1 + (self.col_offset if l1 == 1 else 0), 0)
        return ir.Loc(l1 + 1, c1, c2 if l1 == l2 else 0)

    def err(self, msg: str, x: Any) -> LowerError:
        return LowerError(msg, (x.start_point[0] + 1 + (self.line_offset if self.spec else 0)) if x is not None else 0)

    # -- integer kinds --------------------------------------------------------

    def kinded(self, e: ir.Expr, kind: str | None) -> ir.Expr:
        if kind:
            self.kinds[id(e)] = kind
            self.keep.append(e)
        return e

    def kind_of(self, e: ir.Expr) -> str | None:
        k = self.kinds.get(id(e))
        if k:
            return k
        if isinstance(e, ir.Var):
            return self.fl.kinds.get(e.name) or self.bound_kinds.get(e.name)
        return None

    def kind_of_elems(self, seq: ir.Expr) -> str | None:
        return self.kinds.get(id(seq) * 7 + 1) or (self.fl.elem_kinds.get(seq.name) if isinstance(seq, ir.Var) else None)

    def elems_kinded(self, e: ir.Expr, kind: str | None) -> ir.Expr:
        if kind:
            self.kinds[id(e) * 7 + 1] = kind
            self.keep.append(e)
        return e

    def checked(self, e: ir.Expr, kind: str | None) -> ir.Expr:
        """Integer arithmetic traps on overflow (in code; specs are mathematical)."""
        if not kind or self.spec:
            return self.kinded(e, kind)
        lo, hi = int_range(kind)
        return self.kinded(ir.Builtin(ir.INT, e.loc, "checked", (e, ir.Lit(ir.INT, e.loc, lo), ir.Lit(ir.INT, e.loc, hi), ir.Lit(ir.STR, e.loc, kind))), kind)

    def ranged(self, e: ir.Expr, kind: str | None) -> ir.Expr:
        if not kind or self.spec or e.ty != ir.INT:
            return self.kinded(e, kind)
        return self.kinded(self.fl.in_range(e, kind), kind)

    def nonneg(self, e: ir.Expr) -> ir.Expr:
        if self.spec:
            return self.kinded(e, "Int")
        return self.kinded(ir.Builtin(ir.INT, e.loc, "in_range", (e, ir.Lit(ir.INT, e.loc, 0), ir.Lit(ir.INT, e.loc, INT_MAX))), "Int")

    # -- effects ----------------------------------------------------------------

    def hoist(self, e: ir.Expr) -> ir.Expr:
        """Evaluate an effectful expression now, into a temporary."""
        if self.spec or e.ty == ir.NONE:
            return e
        t = self.fl.fresh("t", e.ty)
        self.pre.append(ir.Assign(e.loc, t, e))
        v = ir.Var(e.ty, e.loc, t)
        if isinstance(e, (ir.New, ir.Call)):
            self.fl.fresh_vars.add(t)
        k = self.kind_of(e)
        if k:
            self.fl.kinds[t] = k
        if id(e) * 7 + 1 in self.kinds:
            self.fl.elem_kinds[t] = self.kinds[id(e) * 7 + 1]
        return v

    def hoist_var(self, e: ir.Expr) -> ir.Expr:
        return e if isinstance(e, (ir.Var, ir.Lit)) or self.spec else self.hoist(e)

    def opaque(self, op: str, parts: list[ir.Expr], ty: ir.Type, loc: ir.Loc) -> ir.Expr:
        return ir.Builtin(ty, loc, "opaque_op", (ir.Lit(ir.STR, loc, op), *[p if p.ty != ir.NONE else ir.Lit(ir.INT, loc, 0) for p in parts]))

    def extern(self, name: str, args: list[ir.Expr], ty: ir.Type, loc: ir.Loc, x: Any) -> ir.Expr:
        if self.spec:
            raise self.err(f"'{name}' is not a checked function (specifications call only checked, pure functions)", x)
        e = ir.Extern(ty, loc, name, tuple(self.hoist_var(a) for a in args))
        if ty == ir.NONE:
            self.pre.append(ir.ExprStmt(loc, e))
            return ir.Lit(ir.NONE, loc, None)
        return self.hoist(e)

    def is_struct(self, ty: ir.Type) -> bool:
        return self.fl.is_struct(ty)

    def copy_value(self, e: ir.Expr) -> ir.Expr:
        """A struct value stored somewhere new gets its own copy (value
        semantics); a fresh one (just built or returned) needs none."""
        if self.spec:
            return e
        if isinstance(e.ty, ir.TOption) and self.is_struct(e.ty.inner) and not _fresh(e) and not (isinstance(e, ir.Var) and e.name in self.fl.fresh_vars):
            src = self.hoist_var(e)
            loc = e.loc
            t = self.fl.fresh("copy", e.ty)
            sub = self.sub()
            inner = sub.copy_value(ir.Builtin(e.ty.inner, loc, "unwrap", (src,)))
            present = tuple(sub.pre) + (ir.Assign(loc, t, ir.Builtin(e.ty, loc, "some", (inner,))),)
            self.pre.append(ir.If(loc, ir.Builtin(ir.BOOL, loc, "is_none", (src,)), (ir.Assign(loc, t, ir.Lit(e.ty, loc, None)),), present))
            return ir.Var(e.ty, loc, t)
        if not self.is_struct(e.ty) or _fresh(e) or isinstance(e, ir.Var) and e.name in self.fl.fresh_vars:
            return e
        assert isinstance(e.ty, ir.TClass)
        decl = self.fl.file_decl(self.pj.types[e.ty.name])
        src = self.hoist_var(e) if not isinstance(e, ir.Var) else e
        args = [self.copy_value(ir.Field(ft, e.loc, src, f)) for f, ft in decl.fields]
        return self.hoist(ir.New(e.ty, e.loc, e.ty.name, tuple(args)))

    # -- dispatch -------------------------------------------------------------------

    def expr(self, x: X, expect: ir.Type | None = None, kind: str | None = None) -> ir.Expr:
        m = getattr(self, "x_" + x.kind, None)
        if m is None:
            raise self.err(f"unsupported expression: {x.kind}", x)
        out = m(x, expect, kind)
        if isinstance(out, TypeRef):
            raise self.err(f"the type '{out.name}' used as a value", x)
        return out

    def x_fixed(self, x: X, expect: Any, kind: Any) -> ir.Expr:
        return x.value

    def x_paren(self, x: X, expect: Any, kind: Any) -> ir.Expr:
        return self.expr(x.e, expect, kind)

    def x_int(self, x: X, expect: Any, kind: Any) -> ir.Expr:
        t = x.text.replace("_", "")
        try:
            v = int(t, 0)
        except ValueError:
            raise self.err(f"unsupported integer literal {t}", x) from None
        if expect == ir.REAL:
            return ir.Lit(ir.REAL, self.loc(x), Fraction(v))
        k = kind if kind else ("Int" if expect in (None, ir.INT) or isinstance(expect, (ir.TOpaque, ir.TOption)) else None)
        if not self.spec and k and not (int_range(k)[0] <= v <= int_range(k)[1]):
            raise self.err(f"integer literal {t} does not fit {k}", x)
        return self.kinded(ir.Lit(ir.INT, self.loc(x), v), k)

    def x_real(self, x: X, expect: Any, kind: Any) -> ir.Expr:
        t = x.text.replace("_", "")
        try:
            v = Fraction(t) if not t.lower().startswith("0x") else Fraction(float.fromhex(t))
        except (ValueError, ZeroDivisionError):
            raise self.err(f"unsupported floating-point literal {t}", x) from None
        return ir.Lit(ir.REAL, self.loc(x), v)

    def x_bool(self, x: X, expect: Any, kind: Any) -> ir.Expr:
        return ir.Lit(ir.BOOL, self.loc(x), x.value)

    def x_nil(self, x: X, expect: Any, kind: Any) -> ir.Expr:
        return ir.Lit(expect if isinstance(expect, ir.TOption) else ir.NONE, self.loc(x), None)

    def x_str(self, x: X, expect: Any, kind: Any) -> ir.Expr:
        loc = self.loc(x)
        if all(isinstance(p, str) for p in x.parts):
            return ir.Lit(ir.STR, loc, "".join(x.parts))
        parts: list[ir.Expr] = []
        for p in x.parts:
            if isinstance(p, str):
                parts.append(ir.Lit(ir.STR, loc, p))
            else:
                v = self.expr(p, None)
                parts.append(v if v.ty not in (ir.NONE,) and not isinstance(v.ty, (ir.TList, ir.TDict, ir.TOption)) else self.fl.coerce(v, ir.TOpaque("")))
        return ir.Builtin(ir.STR, loc, "str_fn", (ir.Lit(ir.STR, loc, "interpolation"), *parts))

    def x_self(self, x: X, expect: Any, kind: Any) -> ir.Expr:
        fl = self.fl
        if fl.init_fields is not None and not fl.materialized:
            if self.spec:
                raise self.err("'self' in a specification of an initializer", x)
            if not fl.top_level:
                raise self.err("an initializer uses 'self' as a whole inside a branch or loop before it is complete", x)
            fl.materialize(self.pre, self.loc(x))
        if "self" not in fl.env:
            raise self.err("'self' outside a method", x)
        return ir.Var(fl.env["self"], self.loc(x), "self")

    def x_super(self, x: X, expect: Any, kind: Any) -> ir.Expr:
        raise self.err("'super' is not modelled", x)

    def x_name(self, x: X, expect: Any, kind: Any) -> Any:
        name = x.id
        loc = self.loc(x)
        fl = self.fl
        if name in self.bound:
            return self.kinded(ir.Var(self.bound[name], loc, name), self.bound_kinds.get(name))
        if self.spec and name == "result" and self.allow_result and fl.resolve("result") is None:
            return self.kinded(ir.Result(fl.info.ret, loc), fl.info.ret_kind)
        r = fl.resolve(name)
        if r is not None and r in fl.env:
            return self.kinded(ir.Var(fl.env[r], loc, r), fl.kinds.get(r))
        t = fl.t
        if t is not None:
            # an implicit 'self.' member
            if fl.init_fields is not None and not fl.materialized and name in fl.init_fields:
                irn = fl.init_fields[name]
                return self.kinded(ir.Var(fl.env[irn], loc, irn), fl.kinds.get(irn))
            if "self" in fl.env or fl.init_fields is not None:
                if self._field(t, name) is not None or self.pj.by_name.get(f"{t.name}.{name}"):
                    return self.member_of(X("self", x.at), name, x, expect)
        if name in self.pj.consts:
            lit, ann = self.pj.consts[name]
            k = ann if ann in INT_KINDS else None
            return self.expr(norm(lit), ir.REAL if ann in REAL_TYPES else expect, k)
        if name in self.pj.types or name in INT_KINDS or name in REAL_TYPES or name in STR_TYPES or name in ("Bool", "Self", "Array", "Dictionary", "Optional", "Set"):
            if name == "Self" and t is not None:
                return TypeRef(t.name, t)
            return TypeRef(name, self.pj.types.get(name))
        if name in self.pj.globals:
            if self.spec:
                raise self.err(f"global variable '{name}' in a specification", x)
            return self.extern(f"global {name}", [], expect if expect is not None and expect != ir.NONE else ir.TOpaque(name), loc, x)
        raise self.err(f"unknown name '{name}'", x)

    def _field(self, t: TypeInfo, name: str) -> ir.Type | None:
        if t.kind not in ("struct", "class") or not isinstance(t.ir_type, ir.TClass):
            return None
        decl = self.fl.file_decl(t)
        return decl.field_type(name)

    # -- operators ----------------------------------------------------------------

    def x_prefix(self, x: X, expect: Any, kind: Any) -> ir.Expr:
        op = x.op
        loc = self.loc(x)
        if op == "-":
            if x.e.kind in ("int", "real"):
                lit = self.expr(x.e, expect, kind)
                assert isinstance(lit, ir.Lit)
                v = -lit.value  # type: ignore[operator]
                k = self.kind_of(lit)
                if k and not self.spec and not (int_range(k)[0] <= v <= int_range(k)[1]):
                    raise self.err(f"integer literal {v} does not fit {k}", x)
                return self.kinded(ir.Lit(lit.ty, loc, v), k)
            a = self.expr(x.e, expect, kind)
            if a.ty == ir.REAL:
                return ir.Unary(ir.REAL, loc, "neg", a)
            if a.ty != ir.INT:
                raise self.err(f"cannot negate {a.ty}", x)
            return self.checked(ir.Unary(ir.INT, loc, "neg", a), self.kind_of(a) or "Int")
        if op == "+":
            return self.expr(x.e, expect, kind)
        if op == "!":
            a = self.expr(x.e, ir.BOOL)
            if a.ty != ir.BOOL:
                raise self.err(f"'!' on {a.ty}", x)
            return ir.Unary(ir.BOOL, loc, "not", a)
        if op == "~":
            a = self.expr(x.e, expect, kind)
            if a.ty != ir.INT:
                raise self.err(f"'~' on {a.ty}", x)
            return self.ranged(self.opaque("bitnot", [a], ir.INT, loc), self.kind_of(a) or "Int")
        if op == "&":
            raise self.err("'&' passes a variable inout; only as a call argument", x)
        raise self.err(f"unsupported prefix operator {op}", x)

    def x_binop(self, x: X, expect: Any, kind: Any) -> ir.Expr:
        op = x.op
        loc = self.loc(x)
        if op in ("&&", "||"):
            a = self.expr(x.l, ir.BOOL)
            s = self.sub()
            b = s.expr(x.r, ir.BOOL)
            if a.ty != ir.BOOL or b.ty != ir.BOOL:
                raise self.err(f"'{op}' needs Bools", x)
            if not s.pre:
                return ir.Binary(ir.BOOL, loc, "and" if op == "&&" else "or", a, b)
            t = self.fl.fresh("sc", ir.BOOL)
            self.pre.append(ir.Assign(loc, t, a))
            tv = ir.Var(ir.BOOL, loc, t)
            guard = tv if op == "&&" else ir.Unary(ir.BOOL, loc, "not", tv)
            self.pre.append(ir.If(loc, guard, tuple(s.pre) + (ir.Assign(loc, t, b),), ()))
            return tv
        if op == "??":
            return self.coalesce(x, expect, kind)
        if op in ("===", "!=="):
            a, b = self.expr(x.l, None), self.expr(x.r, None)
            if not (self.fl.is_class(a.ty) or isinstance(a.ty, ir.TOption) and self.fl.is_class(a.ty.inner)):
                raise self.err("'===' compares class references", x)
            e = ir.Binary(ir.BOOL, loc, "eq", a, self.fl.coerce(b, a.ty))
            return e if op == "===" else ir.Unary(ir.BOOL, loc, "not", e)
        a = self.expr(x.l, expect if op in ("+", "-", "*", "/", "%", "&+", "&-", "&*") else None, kind if op in ("+", "-", "*", "/", "%", "&+", "&-", "&*") else None)
        b_expect = a.ty if a.ty in (ir.INT, ir.REAL) or op in ("==", "!=") else None
        b = self.expr(x.r, b_expect if not isinstance(a.ty, ir.TOpaque) else None, self.kind_of(a) if a.ty == ir.INT else None)
        if a.ty == ir.INT and b.ty == ir.INT and not self.kind_of(a) and self.kind_of(b) and isinstance(a, ir.Lit):
            self.kinded(a, self.kind_of(b))
        if a.ty == ir.REAL and b.ty == ir.INT and isinstance(b, ir.Lit):
            b = ir.Lit(ir.REAL, b.loc, Fraction(b.value))  # type: ignore[arg-type]
        if b.ty == ir.REAL and a.ty == ir.INT and isinstance(a, ir.Lit):
            a = ir.Lit(ir.REAL, a.loc, Fraction(a.value))  # type: ignore[arg-type]
        if op in ("==", "!="):
            e = self.equal(a, b, x)
            return e if op == "==" else ir.Unary(ir.BOOL, loc, "not", e)
        if op in ("<", "<=", ">", ">="):
            if a.ty == b.ty and a.ty in (ir.INT, ir.REAL):
                return ir.Binary(ir.BOOL, loc, BINOPS[op], a, b)
            if a.ty == b.ty == ir.STR:
                return ir.Builtin(ir.BOOL, loc, "str_fn", (ir.Lit(ir.STR, loc, f"swift{op}"), a, b))
            if isinstance(a.ty, ir.TOpaque) or isinstance(b.ty, ir.TOpaque):
                return self.opaque(op, [a, b], ir.BOOL, loc)
            raise self.err(f"cannot compare {a.ty} and {b.ty} with '{op}'", x)
        if op == "+" and a.ty == b.ty == ir.STR:
            return ir.Builtin(ir.STR, loc, "str_concat", (a, b))
        if op == "+" and isinstance(a.ty, ir.TList) and isinstance(b.ty, ir.TList):
            ty = a.ty if a.ty.elem != ir.NONE else b.ty
            return self.elems_kinded(ir.Builtin(ty, loc, "list_concat", (self.fl.coerce(a, ty), self.fl.coerce(b, ty))), self.kind_of_elems(a) or self.kind_of_elems(b))
        if op in ("+", "-", "*", "/", "%"):
            if a.ty != b.ty or a.ty not in (ir.INT, ir.REAL):
                if isinstance(a.ty, ir.TOpaque) or isinstance(b.ty, ir.TOpaque):
                    return self.opaque(op, [a, b], a.ty if not isinstance(a.ty, ir.TOpaque) else b.ty, loc)
                raise self.err(f"'{op}' on {a.ty} and {b.ty}", x)
            if a.ty == ir.REAL:
                if op == "/":  # division by zero gives an infinity or NaN, not a trap
                    nz = ir.Binary(ir.BOOL, loc, "ne", b, ir.Lit(ir.REAL, loc, Fraction(0)))
                    return ir.Ite(ir.REAL, loc, nz, ir.Binary(ir.REAL, loc, "rdiv", a, b), self.opaque("fdiv", [a, b], ir.REAL, loc))
                if op == "%":
                    raise self.err("'%' is not defined on floating point (use truncatingRemainder)", x)
                return ir.Binary(ir.REAL, loc, BINOPS[op], a, b)
            name = {"+": "add", "-": "sub", "*": "mul", "/": "tdiv", "%": "tmod"}[op]
            k = self.kind_of(a) or self.kind_of(b) or kind or "Int"
            if op == "%" and not self.spec and INT_KINDS[k][0]:
                # min % -1 traps like min / -1 does
                a, b = self.kinded(self.hoist_var(a), k), self.kinded(self.hoist_var(b), k)
                self.pre.append(ir.ExprStmt(loc, self.checked(ir.Binary(ir.INT, loc, "tdiv", a, b), k)))
            return self.checked(ir.Binary(ir.INT, loc, name, a, b), k)
        if op in ("&+", "&-", "&*"):
            if a.ty != ir.INT or b.ty != ir.INT:
                raise self.err(f"'{op}' on {a.ty} and {b.ty}", x)
            k = self.kind_of(a) or self.kind_of(b) or kind or "Int"
            signed, bits = INT_KINDS[k]
            raw = ir.Binary(ir.INT, loc, {"&+": "add", "&-": "sub", "&*": "mul"}[op], a, b)
            mod = ir.Lit(ir.INT, loc, 1 << bits)
            if not signed:
                return self.kinded(ir.Binary(ir.INT, loc, "fmod", raw, mod), k)
            h = ir.Lit(ir.INT, loc, 1 << (bits - 1))
            return self.kinded(ir.Binary(ir.INT, loc, "sub", ir.Binary(ir.INT, loc, "fmod", ir.Binary(ir.INT, loc, "add", raw, h), mod), h), k)
        if op in ("&", "|", "^", "<<", ">>", "&<<", "&>>"):
            if a.ty == ir.INT and b.ty == ir.INT:
                return self.ranged(self.opaque(f"bit{op}", [a, b], ir.INT, loc), self.kind_of(a) or "Int")
        raise self.err(f"unsupported operator {op} on {a.ty}", x)

    def coalesce(self, x: X, expect: Any, kind: Any) -> ir.Expr:
        loc = self.loc(x)
        a = self.expr(x.l, ir.TOption(expect) if expect is not None and not isinstance(expect, (ir.TOption, ir.TOpaque)) and expect != ir.NONE else None)
        if not isinstance(a.ty, ir.TOption):
            if isinstance(a.ty, ir.TOpaque):
                s = self.sub()
                d = s.expr(x.r, expect, kind)
                if s.pre:
                    raise self.err("'??' on an unchecked value with a default that does work", x)
                return self.opaque("??", [a, d], d.ty, loc)
            raise self.err(f"'??' needs an optional, not {a.ty}", x)
        k = self.kind_of(a)
        s = self.sub()
        d = s.expr(x.r, a.ty.inner if not isinstance(expect, ir.TOption) else a.ty, k)
        d = self.fl.coerce(d, a.ty.inner) if not isinstance(d.ty, ir.TOption) else d
        rty = d.ty if isinstance(d.ty, ir.TOption) else a.ty.inner
        av = self.hoist_var(a)
        none = ir.Builtin(ir.BOOL, loc, "is_none", (av,))
        present = ir.Builtin(a.ty.inner, loc, "unwrap", (av,))
        if isinstance(rty, ir.TOption):
            present = ir.Builtin(rty, loc, "some", (present,))
        if not s.pre:
            return self.kinded(ir.Ite(rty, loc, none, d, present), k or s.kind_of(d))
        t = self.fl.fresh("coalesce", rty)
        self.pre.append(ir.If(loc, none, tuple(s.pre) + (ir.Assign(loc, t, d),), (ir.Assign(loc, t, present),)))
        if k:
            self.fl.kinds[t] = k
        return ir.Var(rty, loc, t)

    def x_ternary(self, x: X, expect: Any, kind: Any) -> ir.Expr:
        loc = self.loc(x)
        c = self.expr(x.c, ir.BOOL)
        if c.ty != ir.BOOL:
            raise self.err("the condition of '?:' must be a Bool", x)
        st, sf = self.sub(), self.sub()
        a = st.expr(x.t, expect, kind)
        b = sf.expr(x.f, expect or a.ty, kind or st.kind_of(a))
        ty = expect if expect is not None and expect != ir.NONE and not isinstance(expect, ir.TOpaque) else (a.ty if a.ty != ir.NONE else b.ty)
        a, b = self.fl.coerce(a, ty), self.fl.coerce(b, ty)
        if a.ty != b.ty:
            a, b = self._same(a, b, x)
        k = st.kind_of(a) or sf.kind_of(b)
        if not st.pre and not sf.pre:
            return self.kinded(ir.Ite(a.ty, loc, c, a, b), k)
        if self.spec:
            raise self.err("'?:' with effects in a specification", x)
        t = self.fl.fresh("if", a.ty)
        self.pre.append(ir.If(loc, c, tuple(st.pre) + (ir.Assign(loc, t, a),), tuple(sf.pre) + (ir.Assign(loc, t, b),)))
        if k:
            self.fl.kinds[t] = k
        return ir.Var(a.ty, loc, t)

    def _same(self, a: ir.Expr, b: ir.Expr, x: Any) -> tuple[ir.Expr, ir.Expr]:
        if a.ty == b.ty:
            return a, b
        if isinstance(a.ty, ir.TOption) and b.ty == ir.NONE:
            return a, ir.Lit(a.ty, b.loc, None)
        if isinstance(b.ty, ir.TOption) and a.ty == ir.NONE:
            return ir.Lit(b.ty, a.loc, None), b
        if isinstance(a.ty, ir.TOption) and a.ty.inner == b.ty:
            return a, ir.Builtin(a.ty, b.loc, "some", (b,))
        if isinstance(b.ty, ir.TOption) and b.ty.inner == a.ty:
            return ir.Builtin(b.ty, a.loc, "some", (a,)), b
        if isinstance(a, ir.ListLit) and not a.elems and isinstance(b.ty, ir.TList):
            return ir.ListLit(b.ty, a.loc, ()), b
        if isinstance(b, ir.ListLit) and not b.elems and isinstance(a.ty, ir.TList):
            return a, ir.ListLit(a.ty, b.loc, ())
        raise self.err(f"cannot combine {a.ty} and {b.ty}", x)

    # -- equality -------------------------------------------------------------------

    def nfd(self, s: ir.Expr) -> ir.Expr:
        """Swift compares Strings by canonical equivalence: equal normal forms."""
        return ir.Builtin(ir.STR, s.loc, "str_fn", (ir.Lit(ir.STR, s.loc, "nfd"), s))

    def equal(self, a: ir.Expr, b: ir.Expr, x: Any) -> ir.Expr:
        loc = self.loc(x)
        if a.ty != b.ty:
            if isinstance(a.ty, ir.TOpaque) or isinstance(b.ty, ir.TOpaque):
                return self.opaque("==", [a, b], ir.BOOL, loc)
            if self.fl.assignable(a.ty, b.ty) or self.fl.assignable(b.ty, a.ty):
                pass
            else:
                a, b = self._same(a, b, x)
        t = a.ty
        if t in (ir.INT, ir.REAL, ir.BOOL) or isinstance(t, ir.TEnum):
            return ir.Binary(ir.BOOL, loc, "eq", a, b)
        if t == ir.STR:
            if any(isinstance(e, ir.Lit) and e.value == "" for e in (a, b)):
                return ir.Binary(ir.BOOL, loc, "eq", a, b)  # only the empty string is equivalent to ""
            return ir.Binary(ir.BOOL, loc, "eq", self.nfd(a), self.nfd(b))
        if isinstance(t, ir.TOption):
            if isinstance(a, ir.Lit) and a.value is None:
                return ir.Builtin(ir.BOOL, loc, "is_none", (b,))
            if isinstance(b, ir.Lit) and b.value is None:
                return ir.Builtin(ir.BOOL, loc, "is_none", (a,))
            if isinstance(t.inner, (ir.TInt, ir.TReal, ir.TBool, ir.TEnum)):
                return ir.Binary(ir.BOOL, loc, "eq", a, b)
            a, b = self.hoist_var(a), self.hoist_var(b)
            na, nb = ir.Builtin(ir.BOOL, loc, "is_none", (a,)), ir.Builtin(ir.BOOL, loc, "is_none", (b,))
            both_none = ir.Binary(ir.BOOL, loc, "and", na, nb)
            inner = self.equal(ir.Builtin(t.inner, loc, "unwrap", (a,)), ir.Builtin(t.inner, loc, "unwrap", (b,)), x)
            both_some = ir.Binary(ir.BOOL, loc, "and", ir.Binary(ir.BOOL, loc, "and", ir.Unary(ir.BOOL, loc, "not", na), ir.Unary(ir.BOOL, loc, "not", nb)), inner)
            return ir.Binary(ir.BOOL, loc, "or", both_none, both_some)
        if isinstance(t, ir.TRecord):
            info = self.pj.types.get(t.name)
            if info is None or not info.payload:
                raise self.err(f"== on {t}", x)
            if info.custom_eq:
                return self._custom_eq(info, a, b, x)
            a, b = self.hoist_var(a), self.hoist_var(b)
            tag_t = dict(t.fields)["case"]
            ta, tb = ir.Field(tag_t, loc, a, "case"), ir.Field(tag_t, loc, b, "case")
            per_case: ir.Expr = ir.Lit(ir.BOOL, loc, True)
            for i, c in reversed(list(enumerate(info.cases))):
                conj: ir.Expr = ir.Lit(ir.BOOL, loc, True)
                for _, slot, sty, _ in info.payload.get(c.name, []):
                    conj = ir.Binary(ir.BOOL, loc, "and", conj, self.equal(ir.Field(sty, loc, a, slot), ir.Field(sty, loc, b, slot), x))
                per_case = ir.Ite(ir.BOOL, loc, ir.Binary(ir.BOOL, loc, "eq", ta, ir.Lit(tag_t, loc, i)), conj, per_case)
            return ir.Binary(ir.BOOL, loc, "and", ir.Binary(ir.BOOL, loc, "eq", ta, tb), per_case)
        if isinstance(t, ir.TClass):
            info = self.pj.types.get(t.name)
            if info is not None and info.custom_eq:
                return self._custom_eq(info, a, b, x)
            if info is not None and info.kind == "struct" and info.equatable:
                a, b = self.hoist_var(a), self.hoist_var(b)
                decl = self.fl.file_decl(info)
                out: ir.Expr = ir.Lit(ir.BOOL, loc, True)
                for f, ft in decl.fields:
                    out = ir.Binary(ir.BOOL, loc, "and", out, self.equal(ir.Field(ft, loc, a, f), ir.Field(ft, loc, b, f), x))
                return out
            raise self.err(f"== on {t.name}, which has no == telic can see (use === for class identity)", x)
        if isinstance(t, ir.TList):
            if isinstance(t.elem, (ir.TInt, ir.TReal, ir.TBool, ir.TEnum)):
                return ir.Binary(ir.BOOL, loc, "eq", a, b)
            if self.spec:
                raise self.err(f"== on arrays of {t.elem} in a specification", x)
            return self.opaque("==", [self.fl.coerce(a, ir.TOpaque("")), self.fl.coerce(b, ir.TOpaque(""))], ir.BOOL, loc)
        if isinstance(t, ir.TOpaque) or t == ir.NONE:
            return self.opaque("==", [a, b], ir.BOOL, loc)
        raise self.err(f"== on {t} is not supported", x)

    def _custom_eq(self, info: TypeInfo, a: ir.Expr, b: ir.Expr, x: Any) -> ir.Expr:
        fi = self.pj.lookup_fn(f"{info.name}.==", [None, None])
        if fi is None:
            raise self.err(f"cannot find {info.name}.==", x)
        return self.call(fi, None, [(None, _Val(a, x)), (None, _Val(b, x))], x, ir.BOOL)

    # -- try / await / casts ----------------------------------------------------------

    def x_try(self, x: X, expect: Any, kind: Any) -> ir.Expr:
        if self.spec:
            raise self.err("'try' in a specification", x)
        saved = self.try_kind
        self.try_kind = x.op
        try:
            if x.op == "try?":
                inner = x.e
                while inner.kind == "paren":
                    inner = inner.e
                if inner.kind != "call":
                    raise self.err("'try?' is supported on a single call", x)
                v = self.expr(inner, expect.inner if isinstance(expect, ir.TOption) else expect, kind)
                return v
            return self.expr(x.e, expect, kind)
        finally:
            self.try_kind = saved

    def x_await(self, x: X, expect: Any, kind: Any) -> ir.Expr:
        if self.spec:
            raise self.err("'await' in a specification", x)
        v = self.expr(x.e, expect, kind)
        loc = self.loc(x)
        if v.ty == ir.NONE:
            self.pre.append(ir.ExprStmt(loc, ir.Builtin(ir.NONE, loc, "await", (ir.Lit(ir.INT, loc, 0),))))
            return v
        return self.hoist(ir.Builtin(v.ty, loc, "await", (v,)))

    def x_cast(self, x: X, expect: Any, kind: Any) -> ir.Expr:
        loc = self.loc(x)
        ty, k = self.pj.stype(x.type_node, self.fl.info.owner, self.fl.info.generics)
        if x.op == "as":
            v = self.expr(x.e, ty, k)
            if v.ty == ty or isinstance(ty, ir.TOpaque):
                return self.fl.coerce(v, ty)
            if self.fl.assignable(v.ty, ty):
                return self.copy_value(v)
            raise self.err(f"'as' from {v.ty} to {ty}", x)
        if x.op == "is":
            v = self.expr(x.e, None)
            if self.spec:
                raise self.err("'is' in a specification", x)
            return self.extern("is", [self.fl.coerce(v, ir.TOpaque(""))], ir.BOOL, loc, x)
        if x.op == "as?":
            v = self.expr(x.e, None)
            if self.spec:
                raise self.err("'as?' in a specification", x)
            target = ir.TOption(ty) if not isinstance(ty, (ir.TOpaque, ir.TList, ir.TDict, ir.TOption)) else ir.TOpaque(f"{ty}?")
            return self.extern("as?", [self.fl.coerce(v, ir.TOpaque(""))], target, loc, x)
        raise self.err(f"'{x.op}' casts are not supported", x)

    def x_closure(self, x: X, expect: Any, kind: Any) -> ir.Expr:
        if self.spec:
            raise self.err("closures in specifications appear only as the predicate of allSatisfy/contains/map/filter", x)
        fl = self.fl

        def names(n: Any) -> None:
            if n.type == "simple_identifier":
                r = fl.resolve(text(n))
                if r is not None and r in fl.env:
                    fl.escaped.add(r)
            for c in n.children:
                names(c)

        names(x.at)
        return self.opaque("closure", [ir.Lit(ir.STR, self.loc(x), x.src[:40])], ir.TOpaque("closure"), self.loc(x))

    def x_tuple(self, x: X, expect: Any, kind: Any) -> ir.Expr:
        if self.spec:
            raise self.err("tuples in a specification", x)
        parts = [self.expr(v, None) for _, v in x.items]
        return self.opaque("tuple", [p if isinstance(p.ty, ir.TOpaque) else self.fl.coerce(p, ir.TOpaque("")) for p in parts], ir.TOpaque("tuple"), self.loc(x))

    def x_range(self, x: X, expect: Any, kind: Any) -> ir.Expr:
        raise self.err("a range value is supported in for loops, subscripts, patterns and allSatisfy/contains", x)

    def x_stmt_expr(self, x: X, expect: Any, kind: Any) -> ir.Expr:
        if self.spec:
            raise self.err("if/switch in a specification", x)
        if expect is None or expect == ir.NONE:
            raise self.err("an if/switch value needs a known type here", x)
        t = self.fl.fresh("value", expect)
        self.fl.nested(lambda: self.fl.valued_statement(x.node, t, expect, kind, self.pre))
        return ir.Var(expect, self.loc(x), t)

    def x_array(self, x: X, expect: Any, kind: Any) -> ir.Expr:
        loc = self.loc(x)
        et = expect.elem if isinstance(expect, ir.TList) else None
        ek = kind if isinstance(expect, ir.TList) else None
        elems = [self.copy_value(self.expr(c, et, ek)) for c in x.elems]
        for e in elems:
            ek = ek or self.kind_of(e)
        if not elems:
            return ir.ListLit(expect if isinstance(expect, ir.TList) else ir.TList(ir.NONE), loc, ())
        t = et or elems[0].ty
        elems = [self.fl.coerce(e, t) for e in elems]
        if any(e.ty != t and not self.fl.assignable(e.ty, t) for e in elems):
            raise self.err("array elements must have one type", x)
        if isinstance(t, (ir.TList, ir.TDict, ir.TOption, ir.TNone)):
            raise self.err(f"arrays of {t} are not modelled", x)
        return self.elems_kinded(ir.ListLit(ir.TList(t), loc, tuple(elems)), ek or ("Int" if t == ir.INT else None))

    def x_dict(self, x: X, expect: Any, kind: Any) -> ir.Expr:
        loc = self.loc(x)
        if not x.pairs:
            return ir.Builtin(expect if isinstance(expect, ir.TDict) else ir.TDict(ir.NONE, ir.NONE), loc, "dict_lit", ())
        kt = expect.key if isinstance(expect, ir.TDict) else None
        vt = expect.val if isinstance(expect, ir.TDict) else None
        args: list[ir.Expr] = []
        for k, v in x.pairs:
            ke = self.expr(k, kt)
            ve = self.copy_value(self.expr(v, vt, kind))
            kt = kt or ke.ty
            vt = vt or ve.ty
            args += [self.key(self.fl.coerce(ke, kt)), self.fl.coerce(ve, vt)]
        if isinstance(vt, (ir.TList, ir.TDict, ir.TOption)) or not isinstance(kt, (ir.TInt, ir.TStr, ir.TBool, ir.TEnum)):
            raise self.err(f"dictionaries from {kt} to {vt} are not modelled", x)
        if not self.spec:
            # a duplicate key traps
            keys = args[0::2]
            for i in range(len(keys)):
                for j in range(i + 1, len(keys)):
                    self.pre.append(ir.AssertStmt(loc, ir.Clause("assert", ir.Binary(ir.BOOL, loc, "ne", keys[i], keys[j]), loc, "dictionary literal keys are distinct"), native=True))
        return self.elems_kinded(ir.Builtin(ir.TDict(kt, vt), loc, "dict_lit", tuple(args)), kind)  # type: ignore[arg-type]

    def key(self, k: ir.Expr) -> ir.Expr:
        """A dictionary key: a String key is its normal form (keys compare by canonical equivalence)."""
        return self.nfd(k) if k.ty == ir.STR else k

    # -- members -------------------------------------------------------------------

    def x_implicit(self, x: X, expect: Any, kind: Any) -> ir.Expr:
        loc = self.loc(x)
        if isinstance(expect, ir.TOption) and x.name == "none":
            return ir.Lit(expect, loc, None)
        target = expect.inner if isinstance(expect, ir.TOption) else expect
        if isinstance(target, ir.TEnum):
            if x.name not in target.members:
                raise self.err(f"{target.name} has no case {x.name}", x)
            return ir.Lit(target, loc, target.members.index(x.name))
        if isinstance(target, ir.TRecord):
            return self.enum_case(self.pj.types[target.name], x.name, [], x)
        if isinstance(target, (ir.TClass,)) or target in (ir.INT, ir.REAL):
            tn = target.name if isinstance(target, ir.TClass) else ("Int" if target == ir.INT else "Double")
            return self.static_member(TypeRef(tn, self.pj.types.get(tn)), x.name, x, expect)
        if not self.spec and (target is None or isinstance(target, ir.TOpaque)):
            return self.opaque(f"implicit.{x.name}", [], ir.TOpaque(x.name), loc)  # a member of a type telic does not know
        raise self.err(f"'.{x.name}' needs a known enum type here", x)

    def x_member(self, x: X, expect: Any, kind: Any) -> Any:
        base = x.base
        while base.kind == "paren":
            base = base.e
        if base.kind == "name" or base.kind == "member":
            tr = self._type_ref(base)
            if tr is not None:
                return self.static_member(tr, x.name, x, expect)
        if x.opt:
            return self.optional_chain(x, lambda el, b: el.member_value(b, x.name, x, None))
        return self.member_of(base, x.name, x, expect)

    def _type_ref(self, x: X) -> TypeRef | None:
        if x.kind == "name":
            if x.id in self.bound or self.fl.resolve(x.id) is not None:
                return None
            if x.id == "Self" and self.fl.t is not None:
                return TypeRef(self.fl.t.name, self.fl.t)
            if x.id in self.pj.types or x.id in INT_KINDS or x.id in REAL_TYPES or x.id in STR_TYPES or x.id in ("Bool", "Swift", "Array", "Dictionary", "Optional", "Set"):
                return TypeRef(x.id, self.pj.types.get(x.id))
            return None
        if x.kind == "member" and x.base.kind == "name" and x.base.id == "Swift" and self.fl.resolve("Swift") is None:
            return TypeRef(x.name, self.pj.types.get(x.name))
        return None

    def member_of(self, base_x: X, name: str, x: X, expect: Any) -> ir.Expr:
        fl = self.fl
        if base_x.kind == "self" and fl.init_fields is not None and not fl.materialized and name in fl.init_fields:
            irn = fl.init_fields[name]
            if irn not in fl.env:
                raise self.err(f"'self.{name}' is read before it is set", x)
            return self.kinded(ir.Var(fl.env[irn], self.loc(x), irn), fl.kinds.get(irn))
        b = self.expr(base_x, None)
        return self.member_value(b, name, x, expect)

    def member_value(self, b: ir.Expr, name: str, x: X, expect: Any) -> ir.Expr:
        loc = self.loc(x)
        t = b.ty
        if isinstance(t, ir.TOption):
            raise self.err(f"'.{name}' on an optional: unwrap it (!, ?, if let) first", x)
        if isinstance(t, ir.TClass):
            info = self.pj.types.get(t.name)
            if info is not None and info.kind in ("struct", "class"):
                decl = self.fl.file_decl(info)
                ft = decl.field_type(name)
                if ft is not None:
                    v = ir.Field(ft, loc, b, name)
                    k = info.field_kinds.get(name)
                    if isinstance(ft, (ir.TList, ir.TDict)):
                        return self.elems_kinded(v, k)
                    return self.ranged(v, k) if ft == ir.INT else self.kinded(v, k)
            fi = self.pj.member_fn(t.name, name, [])
            if fi is not None and fi.kind in ("getter", "field-getter", "requirement") and not fi.labels:
                return self.call(fi, b, [], x, expect)
            raise self.err(f"{t.name} has no property '{name}' telic can see", x)
        if isinstance(t, (ir.TEnum, ir.TRecord)):
            if name == "rawValue" and isinstance(t, ir.TEnum):
                info = self.pj.types.get(t.name)
                if info is None or info.raw_type is None:
                    raise self.err(f"{t.name} has no raw value", x)
                rt = ir.INT if info.raw_type in INT_KINDS else ir.STR
                return self.kinded(ir.Builtin(rt, loc, "enum_value", (b,)), info.raw_type if rt == ir.INT else None)
            fi = self.pj.member_fn(t.name, name, [])
            if fi is not None and fi.kind == "getter":
                return self.call(fi, b, [], x, expect)
            raise self.err(f"{t.name} has no property '{name}' telic can see", x)
        if isinstance(t, ir.TList):
            n = ir.Builtin(ir.INT, loc, "len", (b,))
            if name == "count":
                return self.nonneg(n)
            if name == "isEmpty":
                return ir.Binary(ir.BOOL, loc, "eq", n, ir.Lit(ir.INT, loc, 0))
            if name in ("first", "last"):
                if isinstance(t.elem, (ir.TList, ir.TDict, ir.TOption)):
                    raise self.err("an optional container is not modelled", x)
                i: ir.Expr = ir.Lit(ir.INT, loc, 0) if name == "first" else ir.Binary(ir.INT, loc, "sub", n, ir.Lit(ir.INT, loc, 1))
                ot = ir.TOption(t.elem)
                nz = ir.Binary(ir.BOOL, loc, "gt", n, ir.Lit(ir.INT, loc, 0))
                return self.kinded(ir.Ite(ot, loc, nz, ir.Builtin(ot, loc, "some", (ir.Index(t.elem, loc, b, i, wrap=False),)), ir.Lit(ot, loc, None)), self.kind_of_elems(b))
            if name == "indices":
                raise self.err("'.indices' is supported in for loops", x)
        if isinstance(t, ir.TDict):
            if name in ("count", "isEmpty"):
                if self.spec:
                    raise self.err(f"Dictionary.{name} in a specification", x)
                n = self.extern("Dictionary.count", [self.fl.coerce(b, ir.TOpaque(""))], ir.INT, loc, x)
                n = self.nonneg(n)
                return n if name == "count" else ir.Binary(ir.BOOL, loc, "eq", n, ir.Lit(ir.INT, loc, 0))
        if t == ir.STR:
            if name == "isEmpty":
                return ir.Binary(ir.BOOL, loc, "eq", b, ir.Lit(ir.STR, loc, ""))
            if name == "count":
                return self.nonneg(self.opaque("String.count", [b], ir.INT, loc))
            return self.str_opaque(name, [b], x, expect)
        if t == ir.INT:
            if name == "magnitude":
                return self.kinded(ir.Builtin(ir.INT, loc, "abs", (b,)), None)
            if name == "description":
                return ir.Builtin(ir.STR, loc, "str_fn", (ir.Lit(ir.STR, loc, "String"), b))
            if self.spec:
                raise self.err(f"Int.{name} in a specification", x)
            return self.ranged(self.opaque(f"Int.{name}", [b], ir.INT, loc), self.kind_of(b) or "Int")
        if t == ir.REAL:
            if self.spec:
                raise self.err(f"Double.{name} in a specification", x)
            ty = ir.BOOL if name.startswith("is") else ir.REAL
            return self.opaque(f"Double.{name}", [b], ty, loc)
        if isinstance(t, ir.TOpaque):
            if self.spec:
                raise self.err(f"'.{name}' of an unchecked value in a specification", x)
            return self.opaque(f"field.{name}", [b], expect if expect is not None and expect != ir.NONE and not isinstance(expect, ir.TOption) else ir.TOpaque(""), loc)
        raise self.err(f"'.{name}' of {t} is not supported", x)

    def str_opaque(self, name: str, args: list[ir.Expr], x: Any, expect: Any) -> ir.Expr:
        """A String operation telic does not interpret: deterministic, unknown
        (or, when its result type is not known, unchecked)."""
        loc = self.loc(x)
        ok = all(a.ty in (ir.STR, ir.INT, ir.BOOL) for a in args)
        ty = ir.BOOL if name.startswith(("has", "is", "contains", "starts", "ends")) else ir.STR if name in STRING_TO_STRING else None
        if not ok or ty is None:
            if self.spec:
                raise self.err(f"String.{name} in a specification", x)
            return self.maybe_throw_extern(f"String.{name}", args, expect, loc, x)
        return ir.Builtin(ty, loc, "str_fn", (ir.Lit(ir.STR, loc, f"String.{name}"), *args))

    def static_member(self, tr: TypeRef, name: str, x: X, expect: Any) -> ir.Expr:
        loc = self.loc(x)
        if tr.name in INT_KINDS and name in ("max", "min"):
            lo, hi = int_range(tr.name)
            return self.kinded(ir.Lit(ir.INT, loc, hi if name == "max" else lo), tr.name)
        if tr.name in INT_KINDS and name == "zero":
            return self.kinded(ir.Lit(ir.INT, loc, 0), tr.name)
        if tr.name in REAL_TYPES and name == "zero":
            return ir.Lit(ir.REAL, loc, Fraction(0))
        info = tr.info
        if info is not None and isinstance(info.ir_type, ir.TEnum) and name in info.ir_type.members:
            return ir.Lit(info.ir_type, loc, info.ir_type.members.index(name))
        if info is not None and isinstance(info.ir_type, ir.TRecord) and any(c.name == name for c in info.cases):
            return self.enum_case(info, name, [], x)
        key = f"{tr.name}.{name}"
        if key in self.pj.consts:
            lit, ann = self.pj.consts[key]
            return self.expr(norm(lit), ir.REAL if ann in REAL_TYPES else expect, ann if ann in INT_KINDS else None)
        fi = self.pj.lookup_fn(key, [])
        if fi is not None and fi.kind == "getter" and fi.static:
            return self.call(fi, None, [], x, expect)
        if self.spec:
            raise self.err(f"'{key}' is not supported in specifications", x)
        return self.extern(key, [], expect if expect is not None and expect != ir.NONE else ir.TOpaque(key), loc, x)

    def enum_case(self, info: TypeInfo, case: str, args: list[tuple[str | None, X]], x: X) -> ir.Expr:
        """Construct a case of an enum with payloads: its tag and payload slots."""
        loc = self.loc(x)
        t = info.ir_type
        assert isinstance(t, ir.TRecord)
        names = [c.name for c in info.cases]
        if case not in names:
            raise self.err(f"{info.name} has no case {case}", x)
        slots = info.payload.get(case, [])
        if len(args) != len(slots):
            raise self.err(f"{info.name}.{case} takes {len(slots)} values", x)
        vals: dict[str, ir.Expr] = {}
        for (lbl, a), (plabel, slot, sty, sk) in zip(args, slots):
            if (lbl or None) != (plabel or None) and plabel is not None:
                raise self.err(f"{info.name}.{case} expects label '{plabel}'", x)
            v = self.fl.coerce(self.copy_value(self.expr(a, sty, sk)), sty)
            if v.ty != sty:
                raise self.err(f"{info.name}.{case}: expected {sty}, got {v.ty}", x)
            vals[slot] = v
        fields: list[tuple[str, ir.Expr]] = []
        for fname, fty in t.fields:
            if fname == "case":
                fields.append((fname, ir.Lit(fty, loc, names.index(case))))
            elif fname in vals:
                fields.append((fname, vals[fname]))
            else:
                fields.append((fname, _default(fty, loc)))
        return ir.RecordLit(t, loc, tuple(fields))

    def optional_chain(self, x: X, then: Any) -> ir.Expr:
        """``base?.rest``: nil if base is nil, else rest applied to its value
        (an optional result is not wrapped twice)."""
        loc = self.loc(x)
        base_x = x.base if x.kind in ("member", "subscript") else x.callee.base
        b = self.expr(base_x, None)
        if not isinstance(b.ty, ir.TOption):
            raise self.err(f"'?.' on {b.ty}, which is not optional", x)
        bv = self.hoist_var(b)
        s = self.sub()
        v = then(s, ir.Builtin(b.ty.inner, loc, "unwrap", (bv,)))
        rty = v.ty if isinstance(v.ty, ir.TOption) else ir.TOption(v.ty) if v.ty != ir.NONE else ir.NONE
        if isinstance(rty, ir.TOption) and isinstance(rty.inner, (ir.TList, ir.TDict, ir.TOption, ir.TOpaque)):
            raise self.err("an optional of this type is not modelled", x)
        none = ir.Builtin(ir.BOOL, loc, "is_none", (bv,))
        present = v if isinstance(v.ty, ir.TOption) or v.ty == ir.NONE else ir.Builtin(rty, loc, "some", (v,))
        if not s.pre:
            if rty == ir.NONE:
                return ir.Lit(ir.NONE, loc, None)
            return self.kinded(ir.Ite(rty, loc, none, ir.Lit(rty, loc, None), present), s.kind_of(v))
        if self.spec:
            raise self.err("'?.' with effects in a specification", x)
        if rty == ir.NONE:
            self.pre.append(ir.If(loc, ir.Unary(ir.BOOL, loc, "not", none), tuple(s.pre), ()))
            return ir.Lit(ir.NONE, loc, None)
        t = self.fl.fresh("chain", rty)
        self.pre.append(ir.If(loc, none, (ir.Assign(loc, t, ir.Lit(rty, loc, None)),), tuple(s.pre) + (ir.Assign(loc, t, present),)))
        k = s.kind_of(v)
        if k:
            self.fl.kinds[t] = k
        return ir.Var(rty, loc, t)

    def x_force(self, x: X, expect: Any, kind: Any) -> ir.Expr:
        v = self.expr(x.e, ir.TOption(expect) if expect is not None and not isinstance(expect, (ir.TOption, ir.TOpaque)) and expect != ir.NONE else None, kind)
        loc = self.loc(x)
        if isinstance(v.ty, ir.TOpaque):
            if self.spec:
                raise self.err("'!' on an unchecked value in a specification", x)
            return self.opaque("!", [v], expect if expect is not None and expect != ir.NONE else ir.TOpaque(""), loc)
        if not isinstance(v.ty, ir.TOption):
            raise self.err(f"'!' on {v.ty}, which is not optional", x)
        u = ir.Builtin(v.ty.inner, loc, "unwrap", (v,))
        k = self.kind_of(v)
        return self.ranged(u, k) if v.ty.inner == ir.INT else self.kinded(u, k)

    def x_subscript(self, x: X, expect: Any, kind: Any) -> ir.Expr:
        if x.opt:
            return self.optional_chain(x, lambda el, b: el.subscript_value(b, x, None))
        b = self.expr(x.base, None)
        return self.subscript_value(b, x, expect)

    def subscript_value(self, b: ir.Expr, x: X, expect: Any) -> ir.Expr:
        loc = self.loc(x)
        args = x.args
        if isinstance(b.ty, ir.TList):
            if len(args) != 1 or args[0][0] is not None:
                raise self.err("unsupported array subscript", x)
            ix = args[0][1]
            while ix.kind == "paren":
                ix = ix.e
            if ix.kind == "range":
                if self.spec:
                    return self.slice(b, ix, x)
                raise self.err("a slice is an ArraySlice, whose indices are not zero-based; wrap it in Array(...)", x)
            i = self.expr(ix, ir.INT, "Int")
            if i.ty != ir.INT:
                raise self.err("an array index must be an Int", x)
            v = ir.Index(b.ty.elem, loc, b, i, wrap=False)
            k = self.kind_of_elems(b)
            return self.ranged(v, k) if b.ty.elem == ir.INT else self.kinded(v, k)
        if isinstance(b.ty, ir.TDict):
            key = self.key(self.fl.coerce(self.expr(args[0][1], b.ty.key), b.ty.key))
            k = self.kind_of_elems(b)
            if len(args) == 2 and args[1][0] == "default":
                d = self.fl.coerce(self.expr(args[1][1], b.ty.val, k), b.ty.val)
                v = ir.Builtin(b.ty.val, loc, "dict_get_or", (b, key, d))
                return self.ranged(v, k) if b.ty.val == ir.INT else self.kinded(v, k)
            if len(args) != 1:
                raise self.err("unsupported dictionary subscript", x)
            return self.kinded(ir.Builtin(ir.TOption(b.ty.val), loc, "dict_get_opt", (b, key)), k)
        if isinstance(b.ty, ir.TOpaque):
            if self.spec:
                raise self.err("subscripting an unchecked value in a specification", x)
            return self.opaque("subscript", [b] + [self.expr(a, None) for _, a in args], expect if expect is not None and expect != ir.NONE else ir.TOpaque(""), loc)
        if b.ty == ir.STR:
            raise self.err("String subscripts (String.Index) are not modelled", x)
        raise self.err(f"subscripting {b.ty}", x)

    def slice(self, b: ir.Expr, rng: X, x: X) -> ir.Expr:
        """``xs[a..<b]`` (as an array): in bounds, or a trap."""
        loc = self.loc(x)
        assert isinstance(b.ty, ir.TList)
        n = ir.Builtin(ir.INT, loc, "len", (b,))
        lo = self.expr(rng.lo, ir.INT) if rng.lo is not None else ir.Lit(ir.INT, loc, 0)
        hi = self.expr(rng.hi, ir.INT) if rng.hi is not None else n
        if rng.op == "..." and rng.hi is not None:
            hi = ir.Binary(ir.INT, loc, "add", hi, ir.Lit(ir.INT, loc, 1))
        if not self.spec:
            b = self.hoist_var(b)
            lo, hi = self.hoist_var(lo), self.hoist_var(hi)
            ok = ir.Binary(ir.BOOL, loc, "and", ir.Binary(ir.BOOL, loc, "le", ir.Lit(ir.INT, loc, 0), lo), ir.Binary(ir.BOOL, loc, "and", ir.Binary(ir.BOOL, loc, "le", lo, hi), ir.Binary(ir.BOOL, loc, "le", hi, ir.Builtin(ir.INT, loc, "len", (b,)))))
            self.pre.append(ir.AssertStmt(loc, ir.Clause("assert", ok, loc, "slice range is within bounds"), native=True))
        return self.elems_kinded(ir.Builtin(b.ty, loc, "slice", (b, lo, hi)), self.kind_of_elems(b))

    # -- calls -------------------------------------------------------------------------

    def x_call(self, x: X, expect: Any, kind: Any) -> ir.Expr:
        callee = x.callee
        while callee.kind == "paren":
            callee = callee.e
        args = list(x.args) + [(None, c) for c in x.trailing]
        loc = self.loc(x)
        if x.opt:
            raise self.err("optional call of a closure is not supported", x)
        if callee.kind == "implicit":
            target = expect.inner if isinstance(expect, ir.TOption) else expect
            if isinstance(expect, ir.TOption) and callee.name == "some" and len(args) == 1:
                v = self.expr(args[0][1], expect.inner, kind)
                return ir.Builtin(expect, loc, "some", (self.fl.coerce(self.copy_value(v), expect.inner),))
            if isinstance(target, ir.TRecord):
                return self.enum_case(self.pj.types[target.name], callee.name, args, x)
            if isinstance(target, ir.TClass):
                return self.construct(TypeRef(target.name, self.pj.types.get(target.name)), args, x, expect) if callee.name == "init" else self.static_call(TypeRef(target.name, self.pj.types.get(target.name)), callee.name, args, x, expect)
            raise self.err(f"'.{callee.name}(...)' needs a known type here", x)
        if callee.kind == "member":
            base = callee.base
            while base.kind == "paren":
                base = base.e
            if base.kind == "self" and callee.name == "init" and self.fl.init_fields is not None and not self.fl.materialized:
                return self.delegate(args, x)
            tr = self._type_ref(base) if base.kind in ("name", "member") else None
            if tr is not None:
                if callee.name == "init":
                    return self.construct(tr, args, x, expect)
                return self.static_call(tr, callee.name, args, x, expect)
            if base.kind == "super":
                raise self.err("calls through 'super' are not modelled", x)
            if callee.opt:
                return self.optional_chain(x, lambda el, b: el.method_value(b, None, callee.name, args, x, None))
            return self.method(base, callee.name, args, x, expect, kind)
        if callee.kind == "name":
            name = callee.id
            r = self.fl.resolve(name)
            if r is not None or name in self.bound:
                if self.spec:
                    raise self.err(f"calling the closure '{name}' is not modelled", x)
                return self._closure_call(name, args, x, expect)
            tr = self._type_ref(callee)
            if tr is not None:
                return self.construct(tr, args, x, expect)
            if name == "old" and self.spec:
                if not self.allow_old:
                    raise self.err("old(...) is only meaningful in '@ensures' and invariants", x)
                e = self.expr(args[0][1], expect, kind)
                return self.kinded(ir.Old(e.ty, loc, e), self.kind_of(e))
            if name == "implies" and self.spec and len(args) == 2:
                return ir.Binary(ir.BOOL, loc, "implies", self.expr(args[0][1], ir.BOOL), self.expr(args[1][1], ir.BOOL))
            labels = [lbl for lbl, _ in args]
            t = self.fl.t
            if t is not None and ("self" in self.fl.env or self.fl.init_fields is not None):
                fi = self.pj.member_fn(t.name, name, labels)
                if fi is not None and fi.kind not in ("init",):
                    if fi.static:
                        return self.call(fi, None, args, x, expect)
                    return self.method(X("self", callee.at), name, args, x, expect, kind)
            fi = self.pj.lookup_fn(name, labels)
            if fi is not None and fi.owner is None:
                return self.call(fi, None, args, x, expect)
            return self.builtin_call(name, args, x, expect, kind)
        if self.spec:
            raise self.err("unsupported call in a specification", x)
        f = self.expr(callee, None)
        return self.extern("closure call", [f] + [self.expr(a, None) for _, a in args], expect if expect is not None and expect != ir.NONE else ir.TOpaque(""), loc, x)

    def delegate(self, args: list[tuple[str | None, X]], x: X) -> ir.Expr:
        """``self.init(...)`` in an initializer: the other initializer builds self."""
        loc = self.loc(x)
        fl = self.fl
        t = fl.t
        assert t is not None
        if not fl.top_level:
            raise self.err("'self.init' inside a branch or loop is not supported", x)
        fi = self.pj.lookup_fn(f"{t.name}.init", [lbl for lbl, _ in args])
        if fi is None:
            raise self.err(f"no initializer of {t.name} matches this 'self.init'", x)
        v = self.call(fi, None, args, x, None)
        obj = v
        if fi.failable:
            if not fl.info.failable:
                raise self.err("a non-failable initializer delegating to a failable one", x)
            self.pre.append(ir.If(loc, ir.Builtin(ir.BOOL, loc, "is_none", (v,)), (ir.Return(loc, ir.Lit(fl.info.ret, loc, None)),), ()))
            obj = ir.Builtin(ir.TClass(t.name), loc, "unwrap", (v,))
        fl.env["self"] = ir.TClass(t.name)
        fl.scopes[0]["self"] = "self"
        fl.used.add("self")
        self.pre.append(ir.Assign(loc, "self", obj))
        fl.materialized = True
        return ir.Lit(ir.NONE, loc, None)

    def _closure_call(self, name: str, args: list[tuple[str | None, X]], x: X, expect: Any) -> ir.Expr:
        f = self.expr(X("name", x.at, id=name), None)
        return self.extern(name, [f] + [self.expr(a, None) for _, a in args], expect if expect is not None and expect != ir.NONE else ir.TOpaque(""), self.loc(x), x)

    def builtin_call(self, name: str, args: list[tuple[str | None, X]], x: X, expect: Any, kind: Any) -> ir.Expr:
        loc = self.loc(x)
        vals = lambda: [a for _, a in args]  # noqa: E731
        if name in ("min", "max") and len(args) >= 2:
            es = [self.expr(a, expect, kind) for a in vals()]
            ty = es[0].ty
            if ty not in (ir.INT, ir.REAL) or any(e.ty != ty for e in es):
                if all(e.ty in (ir.INT, ir.REAL) for e in es):
                    es = [e if e.ty == ir.REAL else (ir.Lit(ir.REAL, e.loc, Fraction(e.value)) if isinstance(e, ir.Lit) else e) for e in es]  # type: ignore[arg-type]
                    ty = ir.REAL
                if any(e.ty != ty for e in es):
                    raise self.err(f"{name} of {', '.join(str(e.ty) for e in es)}", x)
            return self.kinded(ir.Builtin(ty, loc, name, tuple(es)), next((self.kind_of(e) for e in es if self.kind_of(e)), None))
        if name == "abs" and len(args) == 1:
            a = self.expr(args[0][1], expect, kind)
            if a.ty == ir.REAL:
                return ir.Builtin(ir.REAL, loc, "abs", (a,))
            if a.ty == ir.INT:
                return self.checked(ir.Builtin(ir.INT, loc, "abs", (a,)), self.kind_of(a) or "Int")
        if self.spec:
            raise self.err(f"'{name}' is not a checked function", x)
        if name in ("precondition", "assert"):
            c = self.expr(args[0][1], ir.BOOL)
            if c.ty != ir.BOOL:
                raise self.err(f"{name} needs a Bool", x)
            self.pre.append(ir.AssertStmt(loc, ir.Clause("assert", c, loc, " ".join(args[0][1].src.split())), native=True))
            return ir.Lit(ir.NONE, loc, None)
        if name in ("fatalError", "preconditionFailure", "assertionFailure"):
            self.pre.append(ir.AssertStmt(loc, ir.Clause("assert", ir.Lit(ir.BOOL, loc, False), loc, f"{name} is unreachable"), native=True))
            return self._never(expect, loc)
        if name in LOGGING:
            for _, a in args:
                v = self.expr(a, None)
                if not isinstance(v, (ir.Lit, ir.Var)):
                    self.hoist(v) if v.ty != ir.NONE else self.pre.append(ir.ExprStmt(loc, v))
            return ir.Lit(ir.NONE, loc, None)
        if name == "stride":
            raise self.err("stride(...) is supported as the sequence of a for loop", x)
        ev = [self.expr(a, None) for a in vals()]
        return self.maybe_throw_extern(name, ev, expect, loc, x)

    def maybe_throw_extern(self, name: str, args: list[ir.Expr], expect: Any, loc: ir.Loc, x: Any) -> ir.Expr:
        if self.try_kind is not None:
            self.throw_point(None, [a for a in args if not isinstance(a, ir.Lit)], loc, x, name)
        return self.extern(name, args, expect if expect is not None and expect != ir.NONE else ir.TOpaque(f"result of {name}"), loc, x)

    def _never(self, expect: Any, loc: ir.Loc) -> ir.Expr:
        if expect is None or expect == ir.NONE:
            return ir.Lit(ir.NONE, loc, None)
        if isinstance(expect, ir.TOption):
            return ir.Lit(expect, loc, None)
        return ir.Builtin(expect, loc, "from_opaque", (ir.Builtin(ir.TOpaque(""), loc, "opaque_op", (ir.Lit(ir.STR, loc, "never"),)),))

    def construct(self, tr: TypeRef, args: list[tuple[str | None, X]], x: X, expect: Any) -> ir.Expr:
        """``T(...)``: a conversion, a collection, an initializer or the memberwise one."""
        loc = self.loc(x)
        name = tr.name
        labels = [lbl for lbl, _ in args]
        if name in INT_KINDS and len(args) == 1 and labels == [None]:
            v = self.expr(args[0][1], None)
            if v.ty == ir.INT:
                src = self.kind_of(v)
                if src and int_range(src)[0] >= int_range(name)[0] and int_range(src)[1] <= int_range(name)[1]:
                    return self.kinded(v, name)
                return self.checked(v, name) if not self.spec else self.kinded(v, name)
            if v.ty == ir.REAL:
                t = ir.Builtin(ir.INT, loc, "trunc", (v,))
                return self.checked(t, name) if not self.spec else self.kinded(t, name)
            if v.ty == ir.STR:
                if self.spec:
                    raise self.err("Int(String) in a specification", x)
                return self.extern(f"{name}(String)", [v], ir.TOption(ir.INT), loc, x)
            if isinstance(v.ty, ir.TOpaque):
                return self.ranged(self.opaque(name, [v], ir.INT, loc), name)
            raise self.err(f"{name}({v.ty})", x)
        if name in INT_KINDS and labels == ["truncatingIfNeeded"] and not self.spec:
            v = self.expr(args[0][1], ir.INT)
            signed, bits = INT_KINDS[name]
            m = ir.Lit(ir.INT, loc, 1 << bits)
            if not signed:
                return self.kinded(ir.Binary(ir.INT, loc, "fmod", v, m), name)
            h = ir.Lit(ir.INT, loc, 1 << (bits - 1))
            return self.kinded(ir.Binary(ir.INT, loc, "sub", ir.Binary(ir.INT, loc, "fmod", ir.Binary(ir.INT, loc, "add", v, h), m), h), name)
        if name in REAL_TYPES and len(args) == 1 and labels == [None]:
            v = self.expr(args[0][1], ir.REAL)
            if v.ty == ir.INT:
                return ir.Builtin(ir.REAL, loc, "to_real", (v,))
            if v.ty == ir.REAL:
                return v
            if self.spec:
                raise self.err(f"{name}({v.ty}) in a specification", x)
            return self.extern(f"{name}(...)", [v], ir.TOption(ir.REAL) if v.ty == ir.STR else ir.REAL, loc, x)
        if name == "String" and len(args) == 1 and labels == [None]:
            v = self.expr(args[0][1], None)
            if v.ty == ir.STR:
                return v
            if v.ty in (ir.INT, ir.BOOL, ir.REAL):
                return ir.Builtin(ir.STR, loc, "str_fn", (ir.Lit(ir.STR, loc, "String"), v))
            if self.spec:
                raise self.err(f"String({v.ty}) in a specification", x)
            return self.extern("String(...)", [v], ir.STR, loc, x)
        if name == "Bool" and len(args) == 1:
            v = self.expr(args[0][1], ir.BOOL)
            if v.ty == ir.BOOL:
                return v
        if name == "Array":
            if len(args) == 1 and labels == [None]:
                a0 = args[0][1]
                while a0.kind == "paren":
                    a0 = a0.e
                if a0.kind == "subscript" and len(a0.args) == 1 and a0.args[0][1].kind == "range":
                    return self.slice(self.expr(a0.base, None), a0.args[0][1], x)
                v = self.expr(a0, expect)
                if isinstance(v.ty, ir.TList):
                    return v
            if sorted(labels, key=str) == ["count", "repeating"]:
                return self.repeat(dict(args), expect, x)
            if not args and isinstance(expect, ir.TList):
                return ir.ListLit(expect, loc, ())
        if name == "Dictionary" and not args and isinstance(expect, ir.TDict):
            return ir.Builtin(expect, loc, "dict_lit", ())
        info = tr.info
        if info is None:
            if self.spec:
                raise self.err(f"'{name}(...)' is not supported in specifications", x)
            return self.maybe_throw_extern(name, [self.expr(a, None) for _, a in args], expect, loc, x)
        if isinstance(info.ir_type, ir.TEnum) and labels == ["rawValue"]:
            et = info.ir_type
            v = self.hoist_var(self.expr(args[0][1], ir.INT if info.raw_type in INT_KINDS else ir.STR))
            ot = ir.TOption(et)
            out: ir.Expr = ir.Lit(ot, loc, None)
            for i in range(len(et.members) - 1, -1, -1):
                raw = et.values[i]
                lit = ir.Lit(ir.INT if isinstance(raw, int) else ir.STR, loc, raw)
                out = ir.Ite(ot, loc, self.equal(v, lit, x), ir.Builtin(ot, loc, "some", (ir.Lit(et, loc, i),)), out)
            return out
        fi = self.pj.lookup_fn(f"{name}.init", labels)
        if fi is not None:
            return self.call(fi, None, args, x, expect)
        if info.kind == "struct" and not info.has_explicit_init and isinstance(info.ir_type, ir.TClass):
            return self.memberwise(info, args, x)
        if info.kind == "class" and not args and isinstance(info.ir_type, ir.TClass) and all(f.default is not None for f in info.fields) and not self.pj.by_name.get(f"{name}.init"):
            return self.memberwise(info, [], x)
        if self.spec:
            raise self.err(f"'{name}(...)' is not supported in specifications", x)
        if self.pj.by_name.get(f"{name}.init"):
            raise self.err(f"no initializer of {name} takes ({', '.join((lbl or '_') + ':' for lbl in labels)})", x)
        return self.maybe_throw_extern(name, [self.expr(a, None) for _, a in args], expect if expect is not None else info.ir_type, loc, x)

    def memberwise(self, info: TypeInfo, args: list[tuple[str | None, X]], x: X) -> ir.Expr:
        loc = self.loc(x)
        if self.spec:
            raise self.err("specifications cannot create objects", x)
        decl = self.fl.file_decl(info)
        given = dict(args)
        if len(given) != len(args) or None in given:
            raise self.err(f"the memberwise initializer of {info.name} takes labelled arguments", x)
        settable = [f for f in info.fields if not (f.is_let and f.default is not None)]
        order = [f.name for f in settable]
        if [lbl for lbl, _ in args] != [n for n in order if n in given]:
            raise self.err(f"the memberwise initializer of {info.name} takes ({', '.join(n + ':' for n in order)}) in that order", x)
        vals = []
        for fname, fty in decl.fields:
            fi = next(f for f in info.fields if f.name == fname)
            k = info.field_kinds.get(fname)
            if fname in given:
                v = self.copy_value(self.expr(given[fname], fty, k))
            elif fi.default is not None:
                v = self.copy_value(self.expr(norm(fi.default), fty, k))
            else:
                raise self.err(f"{info.name}(...) is missing '{fname}'", x)
            v = self.fl.coerce(v, fty)
            if not self.fl.assignable(v.ty, fty) and not isinstance(fty, ir.TOpaque):
                raise self.err(f"{info.name}.{fname} is {fty}, not {v.ty}", x)
            vals.append(self.hoist_var(v) if not isinstance(v, ir.Lit) else v)
        return self.hoist(ir.New(ir.TClass(info.name), loc, info.name, tuple(vals)))

    def repeat(self, args: dict, expect: Any, x: X) -> ir.Expr:
        loc = self.loc(x)
        if self.spec:
            raise self.err("Array(repeating:count:) in a specification", x)
        et = expect.elem if isinstance(expect, ir.TList) else None
        v = self.hoist_var(self.expr(args["repeating"], et))
        cnt = self.hoist_var(self.expr(args["count"], ir.INT, "Int"))
        self.pre.append(ir.AssertStmt(loc, ir.Clause("assert", ir.Binary(ir.BOOL, loc, "ge", cnt, ir.Lit(ir.INT, loc, 0)), loc, "count >= 0"), native=True))
        t = self.fl.fresh("rep", ir.TList(v.ty))
        i = self.fl.fresh("i", ir.INT)
        self.pre.append(ir.Assign(loc, t, ir.ListLit(ir.TList(v.ty), loc, ())))
        inv = ir.Clause("invariant", ir.Binary(ir.BOOL, loc, "eq", ir.Builtin(ir.INT, loc, "len", (ir.Var(ir.TList(v.ty), loc, t),)), ir.Var(ir.INT, loc, i)), loc, f"len({t}) == {i}", inferred=True)
        allv = ir.Clause("invariant", ir.Quant(ir.BOOL, loc, "forall", f"j${self.fl.tmp}", ir.Lit(ir.INT, loc, 0), ir.Var(ir.INT, loc, i), ir.Binary(ir.BOOL, loc, "eq", ir.Index(v.ty, loc, ir.Var(ir.TList(v.ty), loc, t), ir.Var(ir.INT, loc, f"j${self.fl.tmp}"), wrap=False), v)), loc, "every element is the value", inferred=True)
        body: tuple[ir.Stmt, ...] = (ir.Append(loc, t, self.copy_value(v) if not self.is_struct(v.ty) else v),)
        self.pre.append(ir.ForRange(loc, i, ir.Lit(ir.INT, loc, 0), cnt, (inv, allv) if not self.is_struct(v.ty) else (inv,), body))
        k = self.kind_of(v)
        if k:
            self.fl.elem_kinds[t] = k
        if self.is_struct(v.ty):
            raise self.err("Array(repeating:) of a struct shares one value; not modelled", x)
        return ir.Var(ir.TList(v.ty), loc, t)

    def static_call(self, tr: TypeRef, name: str, args: list[tuple[str | None, X]], x: X, expect: Any) -> ir.Expr:
        info = tr.info
        if info is not None and isinstance(info.ir_type, ir.TRecord) and any(c.name == name for c in info.cases):
            return self.enum_case(info, name, args, x)
        labels = [lbl for lbl, _ in args]
        fi = self.pj.lookup_fn(f"{tr.name}.{name}", labels)
        if fi is not None and fi.static:
            return self.call(fi, None, args, x, expect)
        if self.spec:
            raise self.err(f"'{tr.name}.{name}' is not a checked function", x)
        return self.maybe_throw_extern(f"{tr.name}.{name}", [self.expr(a, None) for _, a in args], expect, self.loc(x), x)

    # -- checked calls ------------------------------------------------------------------

    def raise_condition(self, fi: FnInfo, args: list[ir.Expr], loc: ir.Loc, x: Any) -> ir.Expr | None:
        """When a call to ``fi`` throws: its '@raises', never (a contract
        without one), or unknown (no contract). None: it does not throw."""
        if not fi.throws:
            return None
        fn = fi.fn
        if fn is not None and fn.raises:
            m = {p.name: a for p, a in zip(fi.params, args)}
            from .swift_lower import _subst

            out: ir.Expr = _subst(fn.raises[0].expr, m)
            for r in fn.raises[1:]:
                out = ir.Binary(ir.BOOL, loc, "or", out, _subst(r.expr, m))
            if any(isinstance(e, ir.Old) for e in ir.walk_expr(out)):
                raise self.err(f"'@raises' of {fi.key} uses old()", x)
            return out
        if fn is not None and (fn.requires or fn.ensures or fn.trusted):
            return ir.Lit(ir.BOOL, loc, False)
        return self.opaque(f"throws.{fi.key}.{self.fl.tmp}", [ir.Lit(ir.INT, loc, self._tick())], ir.BOOL, loc)

    def _tick(self) -> int:
        self.fl.tmp += 1
        return self.fl.tmp

    def throw_point(self, fi: FnInfo | None, args: list[ir.Expr], loc: ir.Loc, x: Any, name: str) -> ir.Expr | None:
        """Model the error a call may throw, per the enclosing 'try'. Returns
        the condition under which it throws (for 'try?')."""
        rc = self.raise_condition(fi, args, loc, x) if fi is not None else self.opaque(f"throws.{name}.{self.fl.tmp}", [ir.Lit(ir.INT, loc, self._tick())], ir.BOOL, loc)
        if rc is None or self.try_kind is None:
            if fi is not None and fi.throws and self.try_kind is None and not self.spec:
                raise self.err(f"'{fi.key}' throws; call it with try", x)
            return None
        if isinstance(rc, ir.Lit) and rc.value is False:
            return None
        if self.try_kind == "try":
            self.pre.append(ir.If(loc, rc, (self.before_throw(name, args, loc), ir.Raise(loc, f"an error from {name}", caught=self.fl.do_depth > 0)), ()))
            return None
        if self.try_kind == "try!":
            self.pre.append(ir.AssertStmt(loc, ir.Clause("assert", ir.Unary(ir.BOOL, loc, "not", rc), loc, f"try! {name} does not throw"), native=True))
            return None
        return rc

    def before_throw(self, name: str, args: list[ir.Expr], loc: ir.Loc) -> ir.Stmt:
        """What a call may have changed before it threw: its contract says
        nothing about that state, so whatever it can reach is unknown."""
        return ir.ExprStmt(loc, ir.Extern(ir.NONE, loc, f"{name} up to its throw", tuple(a for a in args if not isinstance(a, ir.Lit))))

    def args_for(self, fi: FnInfo, args: list[tuple[str | None, X]], x: X) -> list[tuple[ir.Param, X | None, Any]]:
        """Match call-site arguments to parameters (defaults filled in)."""
        params = fi.params[1:] if fi.params and fi.params[0].name == "self" and not fi.static and fi.kind != "init" else fi.params
        out = []
        i = 0
        for p, want, dflt in zip(params, fi.labels, fi.defaults):
            if i < len(args) and args[i][0] == want:
                out.append((p, args[i][1], None))
                i += 1
            elif dflt is not None:
                out.append((p, None, dflt))
            else:
                raise self.err(f"'{fi.key}' expects argument '{want or '_'}'", x)
        if i != len(args):
            raise self.err(f"'{fi.key}' takes {len(params)} arguments", x)
        return out

    def call(self, fi: FnInfo, recv: ir.Expr | None, args: list[tuple[str | None, X]], x: X, expect: Any, recv_x: X | None = None) -> ir.Expr:
        loc = self.loc(x)
        vals: list[ir.Expr] = []
        if recv is not None:
            vals.append(recv)
        written: list[tuple[X, ir.Expr]] = []
        for p, ax, dflt in self.args_for(fi, args, x):
            if ax is not None and ax.kind == "prefix" and ax.op == "&":
                if p.name not in fi.inout:
                    raise self.err(f"'&' passes '{p.name}' inout, but it is not an inout parameter", ax)
                v = self.inout_arg(ax.e, p, written, x)
            else:
                if p.name in fi.inout:
                    raise self.err(f"inout parameter '{p.name}' needs '&'", x)
                src = ax if ax is not None else _Default(dflt, x)
                v = self.expr(src if not isinstance(src, _Default) else norm(src.node), p.ty, fi.param_kinds.get(p.name))
                if self.is_struct(v.ty) and self._through_object(ax):
                    v = self.copy_value(v)
            v = self.fl.coerce(v, p.ty)
            if v.ty != p.ty and not self.fl.assignable(v.ty, p.ty) and not (isinstance(p.ty, ir.TList) and isinstance(v.ty, ir.TList) and v.ty.elem == ir.NONE):
                raise self.err(f"argument '{p.name}' of '{fi.key}' expects {p.ty}, got {v.ty}", ax if ax is not None else x)
            vals.append(self.hoist_var(v) if not self.spec and not isinstance(v, ir.Lit) and not (p.name in fi.inout) else v)
        e = ir.Call(fi.ret, loc, fi.key, tuple(vals))
        if self.spec:
            if fi.throws:
                raise self.err(f"'{fi.key}' throws; a specification cannot call it", x)
            return self.kinded(e, fi.ret_kind)
        rc = self.throw_point(fi, vals, loc, x, fi.key)
        if rc is not None:  # try?: nil when it throws
            rty = fi.ret if isinstance(fi.ret, ir.TOption) else ir.TOption(fi.ret) if fi.ret != ir.NONE else ir.NONE
            if isinstance(rty, ir.TOption) and isinstance(rty.inner, (ir.TList, ir.TDict, ir.TOption, ir.TOpaque)):
                raise self.err("try? of this type is not modelled", x)
            t = self.fl.fresh("try", rty) if rty != ir.NONE else None
            ok_body: list[ir.Stmt] = []
            if t is not None:
                call_v: ir.Expr = e if isinstance(fi.ret, ir.TOption) else ir.Builtin(rty, loc, "some", (e,))
                ok_body.append(ir.Assign(loc, t, call_v))
            else:
                ok_body.append(ir.ExprStmt(loc, e))
            thrown = (self.before_throw(fi.key, vals, loc),) + ((ir.Assign(loc, t, ir.Lit(rty, loc, None)),) if t is not None else ())
            self.pre.append(ir.If(loc, rc, thrown, tuple(ok_body)))
            self._write_back(written, loc)
            if t is None:
                return ir.Lit(ir.NONE, loc, None)
            if fi.ret_kind:
                self.fl.kinds[t] = fi.ret_kind
            return ir.Var(rty, loc, t)
        if fi.ret == ir.NONE:
            self.pre.append(ir.ExprStmt(loc, e))
            out: ir.Expr = ir.Lit(ir.NONE, loc, None)
        else:
            out = self.hoist(self.ranged(e, fi.ret_kind) if fi.ret_kind and fi.ret == ir.INT else self.kinded(e, fi.ret_kind))
        self._write_back(written, loc)
        self.closures_ran(loc)
        return out

    def closures_ran(self, loc: ir.Loc) -> None:
        """A closure that escaped may have been called: what it captured may
        have changed. (Unchecked calls do this in the verifier; a checked
        callee can call a closure it is handed too.)"""
        for n in sorted(self.fl.escaped):
            ty = self.fl.env.get(n)
            if ty is None or n in self.fl.lets:
                continue
            k = self.fl.kinds.get(n)
            v: ir.Expr = ir.Extern(ty, loc, "a closure that captured it", ())
            self.pre.append(ir.Assign(loc, n, self.fl.in_range(v, k) if k and ty == ir.INT else v))

    def _through_object(self, ax: X | None) -> bool:
        """Does this argument path read through a class object (which the
        callee could reach and change another way)?"""
        if ax is None:
            return False
        while ax.kind == "paren":
            ax = ax.e
        if ax.kind in ("name", "self"):
            return False
        return True

    def inout_arg(self, ax: X, p: ir.Param, written: list, x: X) -> ir.Expr:
        """``&lvalue`` for an inout parameter."""
        while ax.kind == "paren":
            ax = ax.e
        if isinstance(p.ty, (ir.TList, ir.TDict)):
            if ax.kind != "name":
                raise self.err("inout arrays and dictionaries must be local variables", ax)
            v = self.expr(ax, p.ty)
            if not isinstance(v, ir.Var):
                raise self.err("inout arrays and dictionaries must be local variables", ax)
            self._mutable(v, ax)
            return v
        if isinstance(p.ty, ir.TClass):
            if self.addressable(ax):
                v = self.expr(ax, p.ty)
                if isinstance(v, ir.Var):
                    self._mutable(v, ax)
                return v
            v = self.copy_value(self.expr(ax, p.ty))
            written.append((ax, v))
            return v
        # a scalar inout (not modelled): whatever the callee stores
        v = self.expr(ax, None)
        written.append((ax, ir.Extern(v.ty, self.loc(ax), "write through inout", ())))
        return self.fl.coerce(v, p.ty)

    def _write_back(self, written: list, loc: ir.Loc) -> None:
        for ax, v in written:
            if isinstance(v, ir.Extern):
                k = self.lvalue_type(ax)[1]
                val = self.fl.in_range(v, k) if k and v.ty == ir.INT else v
                self.store(ax, self.hoist(val), loc)
            else:
                self.store(ax, v, loc)

    def _mutable(self, v: ir.Var, x: X) -> None:
        if v.name in self.fl.lets:
            raise self.err(f"'{x.src}' is a constant", x)

    # -- methods ----------------------------------------------------------------------

    def method(self, base_x: X, m: str, args: list[tuple[str | None, X]], x: X, expect: Any, kind: Any) -> ir.Expr:
        q = self.quantifier(base_x, m, args, x)
        if q is not None:
            return q
        b = self.expr(base_x, None)
        return self.method_value(b, base_x, m, args, x, expect)

    def method_value(self, b: ir.Expr, base_x: X | None, m: str, args: list[tuple[str | None, X]], x: X, expect: Any) -> ir.Expr:
        loc = self.loc(x)
        t = b.ty
        labels = [lbl for lbl, _ in args]
        if isinstance(t, (ir.TClass, ir.TEnum, ir.TRecord)):
            fi = self.pj.member_fn(t.name, m, labels)
            if fi is None and isinstance(t, ir.TClass):
                ti = self.pj.types.get(t.name)
                if ti is not None and ti.kind == "protocol" and m in ti.requirements:
                    raise self.err(f"{t.name}.{m} ({', '.join((lbl or '_') + ':' for lbl in labels)}) matches no requirement telic can see", x)
            if fi is not None and not fi.static:
                ptype = self.pj.types.get(fi.owner) if fi.owner else None
                if fi.mutating or (ptype is not None and ptype.kind == "protocol" and m in ptype.mutating_reqs):
                    return self.mutating_call(fi, b, base_x, args, x, expect)
                recv = b
                if self.is_struct(b.ty) and self._through_object(base_x):
                    recv = self.copy_value(b)
                return self.call(fi, recv, args, x, expect)
        if isinstance(t, ir.TList):
            return self.array_method(b, base_x, m, args, x, expect)
        if isinstance(t, ir.TDict):
            return self.dict_method(b, base_x, m, args, x, expect)
        if t == ir.STR:
            vals = [self.expr(a, None) for _, a in args]
            if m in ("hasPrefix", "hasSuffix", "contains") and len(vals) == 1 and vals[0].ty == ir.STR:
                return ir.Builtin(ir.BOOL, loc, "str_fn", (ir.Lit(ir.STR, loc, f"String.{m}"), b, vals[0]))
            if m in ("lowercased", "uppercased") and not vals:
                return ir.Builtin(ir.STR, loc, "str_fn", (ir.Lit(ir.STR, loc, f"String.{m}"), b))
            return self.str_opaque(m, [b, *vals], x, expect)
        if t == ir.INT:
            return self.int_method(b, m, args, x, expect)
        if isinstance(t, ir.TOption):
            if m in ("map", "flatMap"):
                if self.spec:
                    raise self.err(f"Optional.{m} in a specification", x)
                return self.extern(f"Optional.{m}", [self.fl.coerce(b, ir.TOpaque("")) if not isinstance(b.ty, ir.TOpaque) else b], expect if expect is not None and expect != ir.NONE else ir.TOpaque(""), loc, x)
        if self.spec:
            raise self.err(f".{m}() is not supported in specifications here", x)
        vals = [self.expr(a, None) for _, a in args]
        return self.maybe_throw_extern(f"{t}.{m}", [b, *vals], expect, loc, x)

    def mutating_call(self, fi: FnInfo, b: ir.Expr, base_x: X | None, args: list[tuple[str | None, X]], x: X, expect: Any) -> ir.Expr:
        """A mutating method changes its receiver in place: the receiver's own
        object, or a copy that is stored back."""
        ptype = self.pj.types.get(fi.owner) if fi.owner else None
        if ptype is not None and ptype.kind == "protocol":
            if any(self.pj.types.get(c) is not None and self.pj.types[c].kind == "struct" for c in ptype.conformers):
                raise self.err(f"a mutating requirement called through protocol {ptype.name}, which structs conform to, is not modelled", x)
        if self.spec:
            raise self.err("a mutating method in a specification", x)
        if base_x is None:
            raise self.err("a mutating method on a temporary value", x)
        if isinstance(b, ir.Var) and b.name in self.fl.lets and not self.fl.is_class(b.ty):
            raise self.err(f"'{base_x.src}' is a constant", x)
        if self.addressable(base_x) or self.fl.is_class(b.ty):
            return self.call(fi, b, args, x, expect)
        tmp = self.copy_value(b)
        out = self.call(fi, tmp, args, x, expect)
        self.store(base_x, tmp, self.loc(x))
        return out

    def addressable(self, lx: X) -> bool:
        """Is this lvalue a path whose objects belong to it alone (a variable,
        self, or fields of those), so it can be changed in place?"""
        while lx.kind == "paren":
            lx = lx.e
        if lx.kind in ("name", "self"):
            return True
        if lx.kind == "member" and not lx.opt:
            return self.addressable(lx.base)
        return False

    def int_method(self, b: ir.Expr, m: str, args: list[tuple[str | None, X]], x: X, expect: Any) -> ir.Expr:
        loc = self.loc(x)
        k = self.kind_of(b) or "Int"
        if m == "isMultiple" and len(args) == 1 and args[0][0] == "of":
            d = self.hoist_var(self.expr(args[0][1], ir.INT, k))
            zero = ir.Lit(ir.INT, loc, 0)
            # isMultiple(of: 0) is x == 0, not a trap
            nz = ir.Binary(ir.BOOL, loc, "ne", d, zero)
            return ir.Ite(ir.BOOL, loc, nz, ir.Binary(ir.BOOL, loc, "eq", ir.Binary(ir.INT, loc, "tmod", b, ir.Ite(ir.INT, loc, nz, d, ir.Lit(ir.INT, loc, 1))), zero), ir.Binary(ir.BOOL, loc, "eq", b, zero))
        if m == "signum" and not args:
            return self.kinded(ir.Ite(ir.INT, loc, ir.Binary(ir.BOOL, loc, "gt", b, ir.Lit(ir.INT, loc, 0)), ir.Lit(ir.INT, loc, 1), ir.Ite(ir.INT, loc, ir.Binary(ir.BOOL, loc, "lt", b, ir.Lit(ir.INT, loc, 0)), ir.Lit(ir.INT, loc, -1), ir.Lit(ir.INT, loc, 0))), k)
        if m in ("advanced", "distance") and len(args) == 1:
            a = self.expr(args[0][1], ir.INT, k)
            op = "add" if m == "advanced" else "sub"
            return self.checked(ir.Binary(ir.INT, loc, op, b, a) if m == "advanced" else ir.Binary(ir.INT, loc, op, a, b), k)
        if self.spec:
            raise self.err(f"Int.{m} in a specification", x)
        vals = [self.expr(a, None) for _, a in args]
        return self.extern(f"Int.{m}", [b, *vals], expect if expect is not None and expect != ir.NONE else ir.TOpaque(""), loc, x)

    # -- arrays ---------------------------------------------------------------------------

    def array_method(self, b: ir.Expr, base_x: X | None, m: str, args: list[tuple[str | None, X]], x: X, expect: Any) -> ir.Expr:
        loc = self.loc(x)
        t = b.ty
        assert isinstance(t, ir.TList)
        ek = self.kind_of_elems(b)
        labels = [lbl for lbl, _ in args]
        if m == "contains" and labels == [None] and args[0][1].kind != "closure":
            v = self.expr(args[0][1], t.elem, ek)
            if isinstance(t.elem, (ir.TInt, ir.TReal, ir.TBool, ir.TEnum)):
                return ir.Builtin(ir.BOOL, loc, "contains", (b, self.fl.coerce(v, t.elem)))
            if self.spec:
                raise self.err(f"contains on arrays of {t.elem} in a specification", x)
            return self.extern("Array.contains", [self.fl.coerce(b, ir.TOpaque("")), v], ir.BOOL, loc, x)
        if m == "reduce" and len(args) == 2 and args[1][1].kind == "name" and args[1][1].id == "+" or m == "reduce" and len(args) == 2 and _is_plus_closure(args[1][1]):
            init = self.expr(args[0][1], t.elem, ek)
            if t.elem not in (ir.INT, ir.REAL) or init.ty != t.elem:
                raise self.err("reduce(_, +) on numbers only", x)
            total = ir.Builtin(t.elem, loc, "sum", (b,))
            if init.ty == ir.INT:
                total = ir.Binary(ir.INT, loc, "add", init, total)
                if not self.spec:
                    self._no_partial_overflow(b, init, ek or "Int", loc)
                return self.kinded(total, ek or "Int")
            return ir.Binary(ir.REAL, loc, "add", init, total)
        if self.spec:
            raise self.err(f"Array.{m} in a specification", x)
        if m == "append" and labels == [None]:
            v = self.fl.coerce(self.copy_value(self.expr(args[0][1], t.elem if t.elem != ir.NONE else None, ek)), t.elem) if t.elem != ir.NONE else self.expr(args[0][1], None)
            return self.list_update(base_x, b, lambda cur: ir.Builtin(cur.ty, loc, "list_append", (cur, v)), x, append=v)
        if m == "append" and labels == ["contentsOf"]:
            ys = self.fl.coerce(self.expr(args[0][1], t), t)
            if not isinstance(ys.ty, ir.TList):
                raise self.err("append(contentsOf:) of a non-array", x)
            return self.list_update(base_x, b, lambda cur: ir.Builtin(cur.ty, loc, "list_concat", (cur, ys)), x)
        if m == "insert" and labels == [None, "at"]:
            v = self.fl.coerce(self.copy_value(self.expr(args[0][1], t.elem, ek)), t.elem)
            i = self.hoist_var(self.expr(args[1][1], ir.INT, "Int"))
            bv = self.hoist_var(b)
            ln = ir.Builtin(ir.INT, loc, "len", (bv,))
            self._bounds(ir.Binary(ir.BOOL, loc, "and", ir.Binary(ir.BOOL, loc, "le", ir.Lit(ir.INT, loc, 0), i), ir.Binary(ir.BOOL, loc, "le", i, ln)), "insert position is within 0...count", loc)
            new = ir.Builtin(t, loc, "list_concat", (ir.Builtin(t, loc, "list_append", (ir.Builtin(t, loc, "slice", (bv, ir.Lit(ir.INT, loc, 0), i)), v)), ir.Builtin(t, loc, "slice", (bv, i, ln))))
            return self.list_update(base_x, bv, lambda cur: new, x)
        if m in ("removeLast", "removeFirst", "remove", "popLast") and (not args or m == "remove" and labels == ["at"]):
            bv = self.hoist_var(b)
            ln = ir.Builtin(ir.INT, loc, "len", (bv,))
            if m == "remove":
                i = self.hoist_var(self.expr(args[0][1], ir.INT, "Int"))
                self._bounds(ir.Binary(ir.BOOL, loc, "and", ir.Binary(ir.BOOL, loc, "le", ir.Lit(ir.INT, loc, 0), i), ir.Binary(ir.BOOL, loc, "lt", i, ln)), "removal index is within 0..<count", loc)
            elif m == "popLast":
                i = ir.Binary(ir.INT, loc, "sub", ln, ir.Lit(ir.INT, loc, 1))
            else:
                self._bounds(ir.Binary(ir.BOOL, loc, "gt", ln, ir.Lit(ir.INT, loc, 0)), f"{m} on a non-empty array", loc)
                i = ir.Lit(ir.INT, loc, 0) if m == "removeFirst" else ir.Binary(ir.INT, loc, "sub", ln, ir.Lit(ir.INT, loc, 1))
            if m == "popLast":
                ot = ir.TOption(t.elem)
                r = self.fl.fresh("pop", ot)
                new_n = self.fl.fresh("popped", t)
                nonempty = ir.Binary(ir.BOOL, loc, "gt", ln, ir.Lit(ir.INT, loc, 0))
                self.pre.append(ir.If(loc, nonempty, (ir.Assign(loc, r, ir.Builtin(ot, loc, "some", (ir.Index(t.elem, loc, bv, i, wrap=False),))), ir.Assign(loc, new_n, ir.Builtin(t, loc, "slice", (bv, ir.Lit(ir.INT, loc, 0), i)))), (ir.Assign(loc, r, ir.Lit(ot, loc, None)), ir.Assign(loc, new_n, bv))))
                self.list_update(base_x, bv, lambda cur: ir.Var(t, loc, new_n), x)
                if ek:
                    self.fl.kinds[r] = ek
                return ir.Var(ot, loc, r)
            got = self.hoist(ir.Index(t.elem, loc, bv, i, wrap=False))
            new = ir.Builtin(t, loc, "list_concat", (ir.Builtin(t, loc, "slice", (bv, ir.Lit(ir.INT, loc, 0), i)), ir.Builtin(t, loc, "slice", (bv, ir.Binary(ir.INT, loc, "add", i, ir.Lit(ir.INT, loc, 1)), ln))))
            self.list_update(base_x, bv, lambda cur: new, x)
            return self.ranged(got, ek) if t.elem == ir.INT else got
        if m == "removeAll" and not args:
            return self.list_update(base_x, b, lambda cur: ir.ListLit(t, loc, ()), x)
        if m == "swapAt" and len(args) == 2:
            bv = self.hoist_var(b)
            i = self.hoist_var(self.expr(args[0][1], ir.INT, "Int"))
            j = self.hoist_var(self.expr(args[1][1], ir.INT, "Int"))
            a1 = self.hoist(ir.Index(t.elem, loc, bv, i, wrap=False))
            a2 = self.hoist(ir.Index(t.elem, loc, bv, j, wrap=False))
            new = ir.Builtin(t, loc, "list_set", (ir.Builtin(t, loc, "list_set", (bv, i, a2)), j, a1))
            return self.list_update(base_x, bv, lambda cur: new, x)
        if m in ("sort", "reverse", "shuffle") and not args:
            bv = self.hoist_var(b)
            r = self.extern(f"Array.{m}ed", [self.fl.coerce(bv, ir.TOpaque(""))], t, loc, x)
            new = ir.Builtin(t, loc, "same_len", (bv, r))
            self.list_update(base_x, bv, lambda cur: new, x)
            return ir.Lit(ir.NONE, loc, None)
        if m in ("sorted", "reversed", "shuffled") and not args:
            bv = self.hoist_var(b)
            r = self.extern(f"Array.{m}", [self.fl.coerce(bv, ir.TOpaque(""))], t, loc, x)
            return self.elems_kinded(ir.Builtin(t, loc, "same_len", (bv, r)), ek)
        if m in ("map", "filter", "compactMap", "first", "firstIndex", "min", "max", "joined", "prefix", "suffix", "dropFirst", "dropLast", "sum", "forEach", "lastIndex", "last"):
            if m in ("map", "filter"):
                c = self.comprehension(b, m, args, x)
                if c is not None:
                    return c
            vals = [self.expr(a, None) for _, a in args]
            return self.extern(f"Array.{m}", [self.fl.coerce(b, ir.TOpaque("")), *vals], expect if expect is not None and expect != ir.NONE else ir.TOpaque(""), loc, x)
        vals = [self.expr(a, None) for _, a in args]
        if base_x is not None and self.addressable(base_x) and isinstance(b, ir.Var):
            # a mutation telic does not interpret: the array may change arbitrarily
            return self.maybe_throw_extern(f"Array.{m}", [b, *vals], expect, loc, x)
        return self.maybe_throw_extern(f"Array.{m}", [self.fl.coerce(b, ir.TOpaque("")), *vals], expect, loc, x)

    def _bounds(self, ok: ir.Expr, what: str, loc: ir.Loc) -> None:
        self.pre.append(ir.AssertStmt(loc, ir.Clause("assert", ok, loc, what), native=True))

    def _no_partial_overflow(self, b: ir.Expr, init: ir.Expr, kind: str, loc: ir.Loc) -> None:
        """reduce(_, +) traps as soon as a running total overflows."""
        lo, hi = int_range(kind)
        k = f"k${self._tick()}"
        bv = self.hoist_var(b)
        part = ir.Binary(ir.INT, loc, "add", init, ir.Builtin(ir.INT, loc, "sum", (ir.Builtin(bv.ty, loc, "slice", (bv, ir.Lit(ir.INT, loc, 0), ir.Var(ir.INT, loc, k))),)))
        fits = ir.Binary(ir.BOOL, loc, "and", ir.Binary(ir.BOOL, loc, "le", ir.Lit(ir.INT, loc, lo), part), ir.Binary(ir.BOOL, loc, "le", part, ir.Lit(ir.INT, loc, hi)))
        q = ir.Quant(ir.BOOL, loc, "forall", k, ir.Lit(ir.INT, loc, 1), ir.Binary(ir.INT, loc, "add", ir.Builtin(ir.INT, loc, "len", (bv,)), ir.Lit(ir.INT, loc, 1)), fits)
        self.pre.append(ir.AssertStmt(loc, ir.Clause("assert", q, loc, f"{kind} running total does not overflow"), native=True))

    def list_update(self, base_x: X | None, cur: ir.Expr, new: Any, x: X, append: ir.Expr | None = None) -> ir.Expr:
        """Replace an array held at ``base_x`` with ``new(cur)``."""
        loc = self.loc(x)
        if base_x is None:
            raise self.err("mutating a temporary array", x)
        bx = base_x
        while bx.kind == "paren":
            bx = bx.e
        if bx.kind == "name":
            v = self.expr(bx, None)
            if isinstance(v, ir.Var) and v.name in self.fl.env:
                self._mutable(v, bx)
                if append is not None:
                    if isinstance(v.ty, ir.TList) and v.ty.elem == ir.NONE:
                        self.fl.env[v.name] = ir.TList(append.ty)
                    self.pre.append(ir.Append(loc, v.name, append))
                    return ir.Lit(ir.NONE, loc, None)
                self.pre.append(ir.Assign(loc, v.name, new(v)))
                return ir.Lit(ir.NONE, loc, None)
        self.store(bx, new(cur), loc)
        return ir.Lit(ir.NONE, loc, None)

    def comprehension(self, b: ir.Expr, m: str, args: list[tuple[str | None, X]], x: X) -> ir.Expr | None:
        if len(args) != 1 or args[0][1].kind != "closure":
            return None
        name, body = self._closure(args[0][1])
        if name is None:
            return None
        loc = self.loc(x)
        assert isinstance(b.ty, ir.TList)
        s = self.sub()
        s.bound[name] = b.ty.elem
        ek = self.kind_of_elems(b)
        if ek:
            s.bound_kinds[name] = ek
        try:
            v = s.expr(body, ir.BOOL if m == "filter" else None, ek)
        except (LowerError, Unsupported):
            return None
        if s.pre or isinstance(v.ty, (ir.TList, ir.TDict, ir.TNone, ir.TOpaque)):
            return None
        if m == "map":
            return self.elems_kinded(ir.Builtin(ir.TList(v.ty), loc, "comp", (b, ir.Lit(ir.STR, loc, name), v)), s.kind_of(v))
        if v.ty != ir.BOOL:
            return None
        return self.elems_kinded(ir.Builtin(b.ty, loc, "comp", (b, ir.Lit(ir.STR, loc, name), ir.Var(b.ty.elem, loc, name), v)), ek)

    def _closure(self, c: X) -> tuple[str | None, X]:
        """A one-parameter closure: (its parameter's name, its single expression)."""
        body = c.body
        stmts = [s for s in body.children if s.is_named and s.type not in ("comment",)] if body is not None else []
        if len(stmts) != 1:
            raise self.err("closures here are one expression", c)
        s = stmts[0]
        if s.type == "control_transfer_statement" and text(s).startswith("return"):
            val = s.child_by_field_name("result") or next((k for k in s.children if k.is_named), None)
            if val is None:
                raise self.err("closures here return a value", c)
            s = val
        if c.params is None:
            return "$0", norm(s)
        if len(c.params) != 1:
            raise self.err("closures here take one parameter", c)
        return c.params[0], norm(s)

    def quantifier(self, base_x: X, m: str, args: list[tuple[str | None, X]], x: X) -> ir.Expr | None:
        """``xs.allSatisfy { ... }``, ``xs.contains { ... }``,
        ``(a..<b).allSatisfy { ... }``: bounded quantifiers."""
        if m not in ("allSatisfy", "contains") or len(args) != 1 or args[0][1].kind != "closure" or args[0][0] not in (None, "where"):
            return None
        kind = "forall" if m == "allSatisfy" else "exists"
        name, body = self._closure(args[0][1])
        loc = self.loc(x)
        bx = base_x
        while bx.kind == "paren":
            bx = bx.e
        idx = f"{name}$q{self._tick()}"
        s = self.sub()
        if bx.kind == "range":
            if bx.lo is None or bx.hi is None:
                raise self.err("quantify over a bounded range", x)
            lo = self.expr(bx.lo, ir.INT)
            hi = self.expr(bx.hi, ir.INT)
            if bx.op == "...":
                hi = ir.Binary(ir.INT, loc, "add", hi, ir.Lit(ir.INT, loc, 1))
            s.bound[name] = ir.INT
            s.bound_kinds[name] = "Int"
            b = s.expr(body, ir.BOOL)
            if s.pre:
                raise self.err(f"the predicate of {m} must not have effects", x)
            from .swift_lower import _subst

            b = _subst(b, {name: ir.Var(ir.INT, loc, idx)})
            return ir.Quant(ir.BOOL, loc, kind, idx, lo, hi, b)
        seq = self.expr(bx, None)
        if not isinstance(seq.ty, ir.TList):
            return None
        seq = self.hoist_var(seq)
        s.bound[name] = seq.ty.elem
        ek = self.kind_of_elems(seq)
        if ek:
            s.bound_kinds[name] = ek
        b = s.expr(body, ir.BOOL)
        if s.pre:
            raise self.err(f"the predicate of {m} must not have effects", x)
        if b.ty != ir.BOOL:
            raise self.err(f"the predicate of {m} must be a Bool", x)
        return ir.Quant(ir.BOOL, loc, kind, idx, ir.Lit(ir.INT, loc, 0), ir.Builtin(ir.INT, loc, "len", (seq,)), b, elem=name, seq=seq)

    # -- dictionaries -------------------------------------------------------------------------

    def dict_method(self, b: ir.Expr, base_x: X | None, m: str, args: list[tuple[str | None, X]], x: X, expect: Any) -> ir.Expr:
        loc = self.loc(x)
        t = b.ty
        assert isinstance(t, ir.TDict)
        labels = [lbl for lbl, _ in args]
        vk = self.kind_of_elems(b)
        if self.spec:
            raise self.err(f"Dictionary.{m} in a specification", x)
        if m == "removeValue" and labels == ["forKey"]:
            k = self.hoist_var(self.key(self.fl.coerce(self.expr(args[0][1], t.key), t.key)))
            old = self.hoist(ir.Builtin(ir.TOption(t.val), loc, "dict_get_opt", (b, k)))
            self.dict_update(base_x, b, lambda cur: ir.Builtin(t, loc, "dict_remove", (cur, k)), x, remove=k)
            return old
        if m == "updateValue" and labels == [None, "forKey"]:
            v = self.fl.coerce(self.copy_value(self.expr(args[0][1], t.val, vk)), t.val)
            k = self.hoist_var(self.key(self.fl.coerce(self.expr(args[1][1], t.key), t.key)))
            old = self.hoist(ir.Builtin(ir.TOption(t.val), loc, "dict_get_opt", (b, k)))
            self.dict_update(base_x, b, lambda cur: ir.Builtin(t, loc, "dict_set", (cur, k, v)), x, set_=(k, v))
            return old
        if m == "removeAll" and not args:
            self.dict_update(base_x, b, lambda cur: ir.Builtin(t, loc, "dict_lit", ()), x)
            return ir.Lit(ir.NONE, loc, None)
        vals = [self.expr(a, None) for _, a in args]
        return self.maybe_throw_extern(f"Dictionary.{m}", [self.fl.coerce(b, ir.TOpaque("")), *vals], expect, loc, x)

    def dict_update(self, base_x: X | None, cur: ir.Expr, new: Any, x: X, remove: ir.Expr | None = None, set_: tuple | None = None) -> None:
        loc = self.loc(x)
        if base_x is None:
            raise self.err("mutating a temporary dictionary", x)
        bx = base_x
        while bx.kind == "paren":
            bx = bx.e
        if bx.kind == "name":
            v = self.expr(bx, None)
            if isinstance(v, ir.Var) and v.name in self.fl.env:
                self._mutable(v, bx)
                if remove is not None:
                    self.pre.append(ir.DictDel(loc, v.name, remove, strict=False))
                elif set_ is not None:
                    self.pre.append(ir.IndexAssign(loc, v.name, set_[0], set_[1], wrap=False))
                else:
                    self.pre.append(ir.Assign(loc, v.name, new(v)))
                return
        self.store(bx, new(cur), loc)

    # -- assignment ------------------------------------------------------------------------------

    def lvalue_type(self, lx: X) -> tuple[ir.Type | None, str | None]:
        fl = self.fl
        if fl.init_fields is not None and not fl.materialized and lx.kind == "self":
            return ir.TClass(fl.t.name), None  # (evaluating it would build self now)
        try:
            s = self.sub()
            s.pre = []
            v = s.expr(lx, None)
            return v.ty, s.kind_of(v) if v.ty == ir.INT else s.kind_of_elems(v) if isinstance(v.ty, (ir.TList, ir.TDict)) else s.kind_of(v)
        except (LowerError, Unsupported):
            return None, None

    def store(self, lx: X, value: ir.Expr, loc: ir.Loc) -> None:
        """``lx = value``, with value semantics for structs and arrays."""
        if self.spec:
            raise self.err("assignment in a specification", lx)
        fl = self.fl
        while lx.kind == "paren":
            lx = lx.e
        if lx.kind == "name":
            r = fl.resolve(lx.id)
            if r is None or r not in fl.env:
                t = fl.t
                if t is not None and (fl.init_fields is not None and lx.id in fl.init_fields or "self" in fl.env and self._field(t, lx.id) is not None):
                    return self.store(X("member", lx.at, base=X("self", lx.at), name=lx.id, opt=False), value, loc)
                raise self.err(f"unknown variable '{lx.id}'", lx)
            if r in fl.lets:
                raise self.err(f"cannot assign to the constant '{lx.id}'", lx)
            ty = fl.env[r]
            value = fl.coerce(value, ty)
            if isinstance(ty, ir.TList) and ty.elem == ir.NONE and isinstance(value.ty, ir.TList):
                fl.env[r] = ty = value.ty
            if value.ty != ty and not fl.assignable(value.ty, ty):
                raise self.err(f"cannot assign {value.ty} to '{lx.id}' of type {ty}", lx)
            self.pre.append(ir.Assign(loc, r, value))
            return
        if lx.kind == "self":
            # self = T(...) in a mutating method: every field replaced
            if fl.init_fields is not None and not fl.materialized:
                t = fl.t
                assert t is not None
                if not fl.top_level or t.kind != "struct":
                    raise self.err("assigning 'self' in an initializer is supported for structs, outside branches and loops", lx)
                v = self.copy_value(fl.coerce(value, ir.TClass(t.name)))
                if v.ty != ir.TClass(t.name):
                    raise self.err(f"assigning {v.ty} to self", lx)
                fl.env["self"] = ir.TClass(t.name)
                fl.scopes[0]["self"] = "self"
                fl.used.add("self")
                self.pre.append(ir.Assign(loc, "self", v))
                fl.materialized = True
                return
            sv = self.expr(lx, None)
            if not self.is_struct(sv.ty):
                raise self.err("assigning 'self' is supported in mutating methods of structs", lx)
            src = self.hoist_var(fl.coerce(value, sv.ty))
            decl = fl.file_decl(self.pj.types[sv.ty.name])
            for f, ft in decl.fields:
                self.pre.append(ir.FieldAssign(loc, sv, sv.ty.name, f, ir.Field(ft, loc, src, f)))
            return
        if lx.kind == "member" and not lx.opt:
            base = lx.base
            while base.kind == "paren":
                base = base.e
            if base.kind == "self" and fl.init_fields is not None and not fl.materialized and lx.name in fl.init_fields:
                irn = fl.init_fields[lx.name]
                ty = fl.env[irn]
                v = fl.coerce(value, ty)
                if v.ty != ty and not fl.assignable(v.ty, ty) and not isinstance(ty, ir.TOpaque):
                    raise self.err(f"cannot assign {v.ty} to 'self.{lx.name}' of type {ty}", lx)
                self.pre.append(ir.Assign(loc, irn, v))
                return
            tr = self._type_ref(base) if base.kind in ("name", "member") else None
            if tr is not None:
                raise self.err(f"assigning the static property {tr.name}.{lx.name} is not modelled", lx)
            obj = self.expr(base, None)
            if isinstance(obj.ty, ir.TOpaque):
                raise self.err("assigning a property of an unchecked value", lx)
            if not isinstance(obj.ty, ir.TClass):
                raise self.err(f"cannot assign a property of {obj.ty}", lx)
            info = self.pj.types.get(obj.ty.name)
            if info is None or info.kind not in ("struct", "class"):
                raise self.err(f"assigning '{lx.name}' through protocol {obj.ty.name} is not modelled", lx)
            decl = fl.file_decl(info)
            ft = decl.field_type(lx.name)
            if ft is None:
                raise self.err(f"assigning the computed property {obj.ty.name}.{lx.name} is not modelled", lx)
            fi = next(f for f in info.fields if f.name == lx.name)
            if fi.is_let and not (fl.info.kind == "init" and base.kind == "self"):
                raise self.err(f"{obj.ty.name}.{lx.name} is a constant", lx)
            v = fl.coerce(value, ft)
            if v.ty != ft and not fl.assignable(v.ty, ft) and not isinstance(ft, ir.TOpaque):
                raise self.err(f"cannot assign {v.ty} to {obj.ty.name}.{lx.name} of type {ft}", lx)
            if info.kind == "class" or self.addressable(base):
                if isinstance(obj, ir.Var) and obj.name in fl.lets and info.kind == "struct" and obj.name != "self":
                    raise self.err(f"'{base.src}' is a constant", lx)
                if info.kind == "struct" and isinstance(obj, ir.Var) and obj.name == "self" and not (fl.info.mutating or fl.info.kind == "init"):
                    raise self.err("a non-mutating method cannot change self", lx)
                self.pre.append(ir.FieldAssign(loc, obj, obj.ty.name, lx.name, v))
                return
            # a struct reached through an element: copy, change, store back
            tmp = self.copy_value(obj)
            self.pre.append(ir.FieldAssign(loc, tmp, obj.ty.name, lx.name, v))
            self.store(base, tmp, loc)
            return
        if lx.kind == "subscript" and not lx.opt:
            base = lx.base
            seq = self.expr(base, None)
            if isinstance(seq.ty, ir.TList):
                if len(lx.args) != 1:
                    raise self.err("unsupported array subscript", lx)
                i = self.hoist_var(self.expr(lx.args[0][1], ir.INT, "Int"))
                v = fl.coerce(value, seq.ty.elem)
                if isinstance(seq, ir.Var) and (base.kind == "name" or base.kind == "paren"):
                    self._mutable(seq, base)
                    self.pre.append(ir.IndexAssign(loc, seq.name, i, v, wrap=False))
                    return
                seq = self.hoist_var(seq)
                self.pre.append(ir.ExprStmt(loc, ir.Index(seq.ty.elem, loc, seq, i, wrap=False)))  # the index must be in bounds
                return self.store(base, ir.Builtin(seq.ty, loc, "list_set", (seq, i, v)), loc)
            if isinstance(seq.ty, ir.TDict):
                if len(lx.args) == 2 and lx.args[1][0] == "default":
                    k = self.hoist_var(self.key(fl.coerce(self.expr(lx.args[0][1], seq.ty.key), seq.ty.key)))
                    v = fl.coerce(value, seq.ty.val)
                elif len(lx.args) == 1:
                    k = self.hoist_var(self.key(fl.coerce(self.expr(lx.args[0][1], seq.ty.key), seq.ty.key)))
                    if isinstance(value, ir.Lit) and value.value is None:
                        if isinstance(seq, ir.Var) and base.kind == "name":
                            self._mutable(seq, base)
                            self.pre.append(ir.DictDel(loc, seq.name, k, strict=False))
                            return
                        return self.store(base, ir.Builtin(seq.ty, loc, "dict_remove", (seq, k)), loc)
                    if isinstance(value.ty, ir.TOption):
                        raise self.err("assigning an optional into a dictionary is not supported (unwrap it, or assign nil)", lx)
                    v = fl.coerce(value, seq.ty.val)
                else:
                    raise self.err("unsupported dictionary subscript", lx)
                if isinstance(seq, ir.Var) and base.kind == "name":
                    self._mutable(seq, base)
                    self.pre.append(ir.IndexAssign(loc, seq.name, k, v, wrap=False))
                    return
                return self.store(base, ir.Builtin(seq.ty, loc, "dict_set", (seq, k, v)), loc)
            raise self.err(f"assigning an element of {seq.ty}", lx)
        if lx.kind == "fixed":
            raise self.err("unsupported assignment target", lx)
        raise self.err(f"unsupported assignment target '{lx.src}'", lx)

    # -- patterns ------------------------------------------------------------------------------------

    def pattern(self, p: Any, scrut: ir.Expr) -> tuple[ir.Expr, list[tuple[str, ir.Expr, bool]]]:
        """(condition, bindings) of a case pattern against ``scrut``."""
        src = text(p).strip()
        ast = _Pat(src).parse()
        return self._pat(ast, scrut, p, False)

    def _pat(self, ast: tuple, scrut: ir.Expr, p: Any, under_let: bool) -> tuple[ir.Expr, list[tuple[str, ir.Expr, bool]]]:
        loc = self.loc(p)
        true = ir.Lit(ir.BOOL, loc, True)
        k = ast[0]
        if k == "wild":
            return true, []
        if k == "bind":
            return true, [(ast[1], scrut, ast[2])]
        if k == "let":
            return self._pat(ast[2], scrut, p, True) if ast[1] == "let" else self._pat_var(ast[2], scrut, p)
        if k == "name" and under_let:
            return true, [(ast[1], scrut, True)]
        if k == "nil" or k == "case" and ast[2] == "none" and isinstance(scrut.ty, ir.TOption) and not ast[3]:
            if not isinstance(scrut.ty, ir.TOption):
                raise self.err("nil pattern on a non-optional", p)
            return ir.Builtin(ir.BOOL, loc, "is_none", (scrut,)), []
        if k == "opt" or k == "case" and ast[2] == "some" and isinstance(scrut.ty, ir.TOption):
            if not isinstance(scrut.ty, ir.TOption):
                raise self.err("'?' pattern on a non-optional", p)
            sub = ast[1] if k == "opt" else (ast[3][0][1] if len(ast[3]) == 1 else ("wild",) if not ast[3] else None)
            if sub is None:
                raise self.err("'.some' takes one pattern", p)
            u = ir.Builtin(scrut.ty.inner, loc, "unwrap", (scrut,))
            c, binds = self._pat(sub, u, p, under_let)
            present = ir.Unary(ir.BOOL, loc, "not", ir.Builtin(ir.BOOL, loc, "is_none", (scrut,)))
            return (present if isinstance(c, ir.Lit) and c.value is True else ir.Binary(ir.BOOL, loc, "and", present, c)), binds
        if k == "case":
            _, tname, case, subs = ast
            t = scrut.ty
            if isinstance(t, ir.TOption):
                raise self.err(f"'.{case}' pattern on an optional", p)
            if isinstance(t, ir.TEnum):
                if case not in t.members:
                    raise self.err(f"{t.name} has no case {case}", p)
                if subs:
                    raise self.err(f"{t.name}.{case} has no payload", p)
                return ir.Binary(ir.BOOL, loc, "eq", scrut, ir.Lit(t, loc, t.members.index(case))), []
            if isinstance(t, ir.TRecord):
                info = self.pj.types[t.name]
                names = [c.name for c in info.cases]
                if case not in names:
                    raise self.err(f"{t.name} has no case {case}", p)
                tag_t = dict(t.fields)["case"]
                cond: ir.Expr = ir.Binary(ir.BOOL, loc, "eq", ir.Field(tag_t, loc, scrut, "case"), ir.Lit(tag_t, loc, names.index(case)))
                slots = info.payload.get(case, [])
                binds: list[tuple[str, ir.Expr, bool]] = []
                if subs and len(subs) != len(slots):
                    raise self.err(f"{t.name}.{case} has {len(slots)} values", p)
                for (label, sub), (plabel, slot, sty, sk) in zip(subs, slots):
                    fv = ir.Field(sty, loc, scrut, slot)
                    c2, b2 = self._pat(sub, self.ranged(fv, sk) if sty == ir.INT else fv, p, under_let)
                    if not (isinstance(c2, ir.Lit) and c2.value is True):
                        cond = ir.Binary(ir.BOOL, loc, "and", cond, c2)
                    binds += b2
                return cond, binds
            raise self.err(f"'.{case}' pattern on {t}", p)
        if k == "range":
            _, lo_src, op, hi_src = ast
            lo = self._pat_expr(lo_src, scrut, p) if lo_src else None
            hi = self._pat_expr(hi_src, scrut, p) if hi_src else None
            if scrut.ty not in (ir.INT, ir.REAL):
                raise self.err("range patterns on numbers only", p)
            if lo is not None and hi is not None and not (isinstance(lo, ir.Lit) and isinstance(hi, ir.Lit) and lo.value <= hi.value):  # type: ignore[operator]
                raise self.err("range patterns need literal bounds, lower <= upper", p)
            conds = []
            if lo is not None:
                conds.append(ir.Binary(ir.BOOL, loc, "le", lo, scrut))
            if hi is not None:
                conds.append(ir.Binary(ir.BOOL, loc, "le" if op == "..." else "lt", scrut, hi))
            out = conds[0]
            for c in conds[1:]:
                out = ir.Binary(ir.BOOL, loc, "and", out, c)
            return out, []
        if k in ("expr", "name"):
            v = self._pat_expr(ast[1], scrut, p)
            return self.equal(scrut, v, p), []
        raise self.err(f"unsupported pattern '{text(p)}'", p)

    def _pat_var(self, ast: tuple, scrut: ir.Expr, p: Any) -> tuple[ir.Expr, list[tuple[str, ir.Expr, bool]]]:
        c, binds = self._pat(ast, scrut, p, True)
        return c, [(n, e, False) for n, e, _ in binds]

    def _pat_expr(self, src: str, scrut: ir.Expr, p: Any) -> ir.Expr:
        _, node = parse_expr_src(src)
        if node is None:
            raise self.err(f"cannot parse the pattern '{src}'", p)
        x = norm(node)
        s = self.sub()
        s.spec = True  # a pattern value has no effects
        v = s.expr(_relocated(x, p), scrut.ty if scrut.ty in (ir.INT, ir.REAL, ir.STR) or isinstance(scrut.ty, ir.TEnum) else None, self.kind_of(scrut))
        return v


def parse_expr_src(src: str) -> tuple[Any, Any]:
    from .swift_syntax import parse_expression

    return parse_expression(src)


def _relocated(x: X, anchor: Any) -> X:
    """Report a synthetic expression at ``anchor``."""

    def walk(y: Any) -> None:
        if isinstance(y, X):
            y.at = _Loc(y.at, anchor)
            for v in list(y.__dict__.values()):
                if isinstance(v, X):
                    walk(v)
                elif isinstance(v, list):
                    for z in v:
                        if isinstance(z, X):
                            walk(z)
                        elif isinstance(z, tuple):
                            for w in z:
                                if isinstance(w, X):
                                    walk(w)

    walk(x)
    return x


class _Loc:
    def __init__(self, node: Any, anchor: Any):
        self._n = node
        self.start_point = anchor.start_point
        self.end_point = anchor.end_point

    def __getattr__(self, name: str) -> Any:
        return getattr(self._n, name)


class _Val(X):
    """A lowered value passed where an expression is expected."""

    def __init__(self, value: ir.Expr, like: Any):
        super().__init__("fixed", like.at if isinstance(like, X) else like, value=value)


class _Default:
    def __init__(self, node: Any, at: X):
        self.node = node
        self.at = at


class _Pat:
    """A small parser for case patterns (tree-sitter-swift's pattern trees
    are too loose to lower directly)."""

    def __init__(self, src: str):
        self.s = src
        self.i = 0

    def ws(self) -> None:
        while self.i < len(self.s) and self.s[self.i].isspace():
            self.i += 1

    def peek(self, t: str) -> bool:
        self.ws()
        return self.s.startswith(t, self.i)

    def word(self) -> str | None:
        self.ws()
        m = re.match(r"[A-Za-z_]\w*", self.s[self.i :])
        if not m:
            return None
        return m.group(0)

    def eat(self, t: str) -> None:
        self.ws()
        if not self.s.startswith(t, self.i):
            raise Unsupported(f"unsupported pattern '{self.s}'", None)
        self.i += len(t)

    def parse(self) -> tuple:
        p = self.pat()
        self.ws()
        if self.i != len(self.s):
            raise Unsupported(f"unsupported pattern '{self.s}'", None)
        return p

    def pat(self) -> tuple:
        w = self.word()
        if w in ("let", "var"):
            self.i += len(w)
            self.ws()
            return ("let", w, self.pat())
        if w == "_" and not re.match(r"_\w", self.s[self.i:]):
            self.i += 1
            return self._opt(("wild",))
        if self.peek(".") and not self.peek(".."):
            self.eat(".")
            name = self.word()
            if name is None:
                raise Unsupported(f"unsupported pattern '{self.s}'", None)
            self.i += len(name)
            return self._case(None, name)
        if w is not None and w[0].isupper() and w not in ("Int", "Double"):
            j = self.i + len(w)
            rest = self.s[j:].lstrip()
            if rest.startswith("."):
                self.i = j
                self.eat(".")
                name = self.word()
                if name is None:
                    raise Unsupported(f"unsupported pattern '{self.s}'", None)
                self.i += len(name)
                return self._case(w, name)
        if w == "nil":
            self.i += 3
            return ("nil",)
        if w is not None and w not in ("true", "false") and re.fullmatch(r"[a-z_]\w*", w):
            self.i += len(w)
            rest = self.s[self.i :].lstrip()
            if not rest or rest[0] in ",)?":
                return self._opt(("name", w))
            self.i -= len(w)
        # an expression pattern (a literal or a range), up to ',' or ')' at depth 0
        start = self.i
        depth = 0
        instr = False
        while self.i < len(self.s):
            ch = self.s[self.i]
            if ch == '"':
                instr = not instr
            elif not instr:
                if ch in "([":
                    depth += 1
                elif ch in ")]":
                    if depth == 0:
                        break
                    depth -= 1
                elif ch == "," and depth == 0:
                    break
            self.i += 1
        e = self.s[start : self.i].strip()
        for op in ("..<", "..."):
            if op in e and not e.startswith('"'):
                lo, hi = e.split(op, 1)
                return ("range", lo.strip(), op, hi.strip())
        return ("expr", e)

    def _opt(self, p: tuple) -> tuple:
        if self.peek("?"):
            self.eat("?")
            return ("opt", p)
        return p

    def _case(self, tname: str | None, name: str) -> tuple:
        subs: list[tuple[str | None, tuple]] = []
        if self.peek("("):
            self.eat("(")
            while True:
                self.ws()
                label = None
                m = re.match(r"([A-Za-z_]\w*)\s*:(?!:)", self.s[self.i :])
                if m and m.group(1) not in ("let", "var"):
                    label = m.group(1)
                    self.i += m.end()
                subs.append((label, self.pat()))
                if self.peek(","):
                    self.eat(",")
                    continue
                self.eat(")")
                break
        return self._opt(("case", tname, name, subs))


def _default(t: ir.Type, loc: ir.Loc) -> ir.Expr:
    if t == ir.INT:
        return ir.Lit(ir.INT, loc, 0)
    if t == ir.REAL:
        return ir.Lit(ir.REAL, loc, Fraction(0))
    if t == ir.BOOL:
        return ir.Lit(ir.BOOL, loc, False)
    if t == ir.STR:
        return ir.Lit(ir.STR, loc, "")
    if isinstance(t, ir.TEnum):
        return ir.Lit(t, loc, 0)
    if isinstance(t, ir.TOption):
        return ir.Lit(t, loc, None)
    if isinstance(t, ir.TRecord):
        return ir.RecordLit(t, loc, tuple((f, _default(ft, loc)) for f, ft in t.fields))
    if isinstance(t, ir.TClass):
        return ir.Lit(ir.INT, loc, 0)  # an unused slot: never read
    raise LowerError(f"no default value for a payload of type {t}", loc.line)


def _fresh(e: ir.Expr) -> bool:
    """Built just now, or returned by a checked function: nothing else holds it."""
    return isinstance(e, (ir.New, ir.Call))


def _is_plus_closure(c: X) -> bool:
    if c.kind != "closure" or c.body is None:
        return False
    t = re.sub(r"\s+", "", text(c.body))
    return t in ("$0+$1",)
