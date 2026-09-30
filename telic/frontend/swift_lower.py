"""Lowering Swift function bodies and contracts to the IR (see swift.py for
the model of Swift's values)."""

from __future__ import annotations

import dataclasses
import re
from fractions import Fraction
from typing import Any

from .. import ir
from ..contracts import FUNCTION_KEYWORDS, LOOP_KEYWORDS, STATEMENT_KEYWORDS, ContractLine, ContractSyntaxError, parse_aim_directive
from .swift import INT_KINDS, LOGGING, FnInfo, LowerError, Project, TypeInfo, _base_name, _line, int_range
from .swift_syntax import Unsupported, X, named, norm, parse_expression, text

BINOPS = {"+": "add", "-": "sub", "*": "mul", "<": "lt", "<=": "le", ">": "gt", ">=": "ge"}
EXPR_STMT_SKIP = {"comment", "multiline_comment"}


class FunctionLowerer:
    def __init__(self, pj: Project, info: FnInfo):
        self.pj = pj
        self.info = info
        self.file = pj.files[info.path]
        self.t: TypeInfo | None = pj.types.get(info.owner) if info.owner else None
        self.env: dict[str, ir.Type] = {p.name: p.ty for p in info.params}
        self.kinds: dict[str, str] = dict(info.param_kinds)
        self.elem_kinds: dict[str, str] = dict(info.elem_kinds)
        self.scopes: list[dict[str, str]] = [{p.name: p.name for p in info.params}]
        self.used: set[str] = {p.name for p in info.params}
        self.lets: set[str] = {p.name for p in info.params if p.name not in info.inout}
        self.tmp = 0
        self.aims: list[str] = []
        n = info.node
        self.lo, self.hi = _line(n), n.end_point[0] + 1
        self.local_contracts = [cl for cl in self.file.contracts if self.lo <= cl.line <= self.hi]
        self.escaped: set[str] = set()
        self.fresh_vars: set[str] = set()  # temporaries holding a struct nothing else holds
        self.do_depth = 0
        self.loop_depth = 0
        self.switch_depth: list[int] = []  # loop depth at each enclosing switch
        # an initializer builds 'self' field by field before it exists
        self.init_fields: dict[str, str] | None = None
        self.materialized = False
        self.top_level = True
        self.fn: ir.Function = info.fn if info.fn is not None else self._blank()

    def _blank(self) -> ir.Function:
        n = self.info.node
        return ir.Function(self.info.key, ir.Loc(_line(n), n.start_point[1]), n.end_point[0] + 1, self.info.params, self.info.ret, source=text(n), exported=self.info.exported)

    def err(self, msg: str, node: Any) -> LowerError:
        return LowerError(msg, _line(node) if node is not None else 0)

    def loc(self, n: Any) -> ir.Loc:
        (l1, c1), (l2, c2) = n.start_point, n.end_point
        return ir.Loc(l1 + 1, c1, c2 if l1 == l2 else 0)

    def fresh(self, base: str, ty: ir.Type) -> str:
        self.tmp += 1
        name = f"{base}${self.tmp}"
        self.env[name] = ty
        return name

    # -- contracts ------------------------------------------------------

    def header_lines(self, info: FnInfo) -> list[ContractLine]:
        f = self.pj.files[info.path]
        node = info.node
        start = _line(node)
        by_line = {ln: cl for cl in f.contracts for ln in cl.raw_lines}
        above: list[ContractLine] = []
        ln = start - 1
        while ln >= 1:
            t = f.lines[ln - 1].strip()
            if not (t.startswith("//") or t.startswith("@") or t == ""):
                break
            if t == "" and not above:
                break
            cl = by_line.get(ln)
            if cl is not None and cl.keyword in FUNCTION_KEYWORDS and cl not in above:
                above.append(cl)
            ln -= 1
        above.reverse()
        body = info.body
        if body is not None and body.type == "statements":
            first = next((c for c in body.children if c.is_named and c.type not in EXPR_STMT_SKIP), None)
            limit = _line(first) if first is not None else body.end_point[0] + 1
            braces = node.child_by_field_name("body") or node.child_by_field_name("computed_value") or next((c for c in node.children if c.type == "computed_property"), None)
            top = _line(braces) if braces is not None else _line(body)
            above += [cl for cl in f.contracts if top <= cl.line < limit and cl.keyword in FUNCTION_KEYWORDS and cl not in above and _line(node) <= cl.line]
        elif body is not None:
            above += [cl for cl in f.contracts if _line(body) <= cl.line <= body.end_point[0] + 1 and cl.keyword in FUNCTION_KEYWORDS and cl not in above]
        return above

    def contracts(self) -> ir.Function:
        info = self.info
        self.fn = self._blank()
        own = self.header_lines(info)
        for cl in own:
            cl.consumed = True
            try:
                self._function_contract(cl)
            except (LowerError, ContractSyntaxError) as e:
                self.fn.unsupported.append((f"contract: {e}", ir.Loc(getattr(e, "line", cl.line) or cl.line)))
            except Unsupported as e:
                self.fn.unsupported.append((f"contract: {e}", ir.Loc(cl.line)))
        info.contract_lines = own
        req = info.inherit
        if req is not None:
            theirs = [cl for cl in self.header_lines(req) if cl.keyword in ("requires", "ensures", "raises")]
            mine = [cl for cl in own if cl.keyword in ("requires", "ensures", "raises")]
            if mine and [(c.keyword, c.payload) for c in mine] != [(c.keyword, c.payload) for c in theirs]:
                self.fn.unsupported.append((f"implements {req.key} with a different contract; calls through {req.owner} are checked against {req.key}'s, so keep it (or remove this one to inherit it)", self.fn.loc))
            elif not mine and theirs:
                # the requirement's contract, its parameters renamed to ours by position
                rename = {rp.name: mp.name for rp, mp in zip(req.params, info.params)}
                saved = self.scopes
                self.scopes = [{**{p.name: p.name for p in info.params}, **{k: v for k, v in rename.items()}}]
                try:
                    for cl in theirs:
                        try:
                            self._function_contract(cl, file=self.pj.files[req.path])
                        except (LowerError, ContractSyntaxError, Unsupported) as e:
                            self.fn.unsupported.append((f"contract of {req.key}: {e}", self.fn.loc))
                finally:
                    self.scopes = saved
        if info.kind == "requirement" or info.body is None and info.kind not in ("field-getter",):
            self.fn.trusted = True
        return self.fn

    def _function_contract(self, cl: ContractLine, file: Any = None) -> None:
        kw = cl.keyword
        if kw == "aim":
            ids, txt = parse_aim_directive(cl)
            if txt is not None:
                self.file.module.aims.append(ir.AimDecl(ids[0], txt, ir.Loc(cl.line, cl.col)))
            for i in ids:
                if i not in self.aims:
                    self.aims.append(i)
            self.current_aims = ids
            self.fn.aims = list(self.aims)
            return
        if kw == "mirrors":
            self.fn.mirrors.append((cl.payload.strip(), ir.Loc(cl.line, cl.col)))
            return
        if kw == "trusted":
            self.fn.trusted = True
            return
        if kw == "pure":
            return
        tags = tuple(cl.tags) or tuple(getattr(self, "current_aims", ()))
        for t in tags:
            if t not in self.aims:
                self.aims.append(t)
        self.fn.aims = list(self.aims)
        if kw == "requires":
            self.fn.requires.append(self.clause(cl, "requires", tags))
        elif kw == "ensures":
            self.fn.ensures.append(self.clause(cl, "ensures", tags))
        elif kw == "decreases":
            self.fn.decreases = self.clause(cl, "decreases", tags, expect=ir.INT)
        elif kw == "raises":
            if not self.info.throws:
                raise LowerError("'@raises' on a function that does not throw", cl.line)
            self.fn.raises.append(self.clause(cl, "raises", tags))

    def clause(self, cl: ContractLine, kind: str, tags: tuple[str, ...] = (), expect: ir.Type = ir.BOOL) -> ir.Clause:
        txt = cl.payload
        if not txt:
            raise LowerError(f"empty '@{kind}'", cl.line)
        tree, node = parse_expression(txt)
        if node is None:
            raise LowerError(f"cannot parse '@{kind}' as a Swift expression", cl.line)
        el = ExprLowerer(self, spec=True, line_offset=cl.line - 2, col_offset=cl.payload_col, allow_old=kind in ("ensures", "invariant"), allow_result=kind == "ensures")
        e = el.expr(norm(node), expect)
        if el.pre:
            raise LowerError(f"'@{kind}' must be a pure expression", cl.line)
        if expect == ir.BOOL and e.ty != ir.BOOL:
            raise LowerError(f"'@{kind}' must be a boolean expression", cl.line)
        if expect == ir.INT and e.ty != ir.INT:
            raise LowerError(f"'@{kind}' must be an integer expression", cl.line)
        loc = ir.Loc(cl.line, cl.payload_col, cl.payload_col + len(txt) if "\n" not in txt else 0)
        return ir.Clause(kind, e, loc, " ".join(txt.split()), tags)

    def invariant(self, cl: ContractLine) -> ir.Clause:
        c = self.clause(cl, "invariant", tuple(cl.tags))
        for x in ir.walk_expr(c.expr):
            if isinstance(x, ir.Field) and isinstance(x.obj.ty, ir.TClass) and not (isinstance(x.obj, ir.Var) and x.obj.name == "self"):
                raise LowerError("an invariant may only read fields of 'self', not of other objects", cl.line)
            if isinstance(x, ir.Call):
                raise LowerError("an invariant may not call functions; write the condition on self's fields", cl.line)
        return c

    def _loop_contracts(self, loop: Any, body: Any) -> list[ContractLine]:
        out: list[ContractLine] = []
        by_line = {ln: cl for cl in self.local_contracts for ln in cl.raw_lines}
        ln = loop.start_point[0]
        while ln >= 1:
            t = self.file.lines[ln - 1].strip()
            if not t.startswith("//"):
                break
            cl = by_line.get(ln)
            if cl is not None and cl.keyword in LOOP_KEYWORDS and not cl.consumed and cl not in out:
                out.append(cl)
            ln -= 1
        out.reverse()
        if body is not None:
            first = next((c for c in body.children if c.is_named and c.type not in EXPR_STMT_SKIP), None)
            limit = _line(first) if first is not None else body.end_point[0] + 1
            out += [cl for cl in self.local_contracts if _line(loop) <= cl.line < limit and cl.keyword in LOOP_KEYWORDS and not cl.consumed and cl not in out]
        for cl in out:
            cl.consumed = True
        return out

    def _loop_clauses(self, cls: list[ContractLine]) -> tuple[tuple[ir.Clause, ...], ir.Clause | None]:
        invs, dec = [], None
        for cl in cls:
            if cl.keyword == "invariant":
                invs.append(self.clause(cl, "invariant", tuple(cl.tags)))
            elif cl.keyword == "decreases":
                dec = self.clause(cl, "decreases", tuple(cl.tags), expect=ir.INT)
            else:
                raise LowerError(f"'@{cl.keyword}' is not supported on Swift loops", cl.line)
        return tuple(invs), dec

    def _stmt_contracts(self, lo: int, hi: int, out: list[ir.Stmt]) -> None:
        for cl in self.local_contracts:
            if not cl.consumed and lo < cl.line <= hi and cl.keyword in STATEMENT_KEYWORDS:
                cl.consumed = True
                try:
                    c = self.clause(cl, cl.keyword, tuple(cl.tags))
                except (LowerError, Unsupported) as e:
                    self.fn.unsupported.append((str(e), ir.Loc(getattr(e, "line", 0) or cl.line)))
                    out.append(ir.Unsupported(ir.Loc(cl.line), str(e)))
                    continue
                out.append(ir.AssertStmt(c.loc, c) if cl.keyword == "assert" else ir.AssumeStmt(c.loc, c))

    # -- the body ---------------------------------------------------------

    def lower(self) -> ir.Function:
        info = self.info
        fn = self.fn = info.fn if info.fn is not None else self.contracts()
        for msg, line in info.problems:
            fn.unsupported.append((msg, ir.Loc(line)))
        if info.kind == "field-getter":
            loc = fn.loc
            self_v = ir.Var(info.params[0].ty, loc, "self")
            fn.body = [ir.Return(loc, ir.Field(info.ret, loc, self_v, info.field_name or ""))]
            fn.locals = dict(self.env)
            return fn
        if fn.trusted and (info.body is None or info.kind == "requirement"):
            return fn
        if fn.trusted:
            return fn
        if _has_error(info.node):
            raise LowerError("this function does not parse (a syntax error, or Swift syntax telic's parser does not know)", _line(_first_err(info.node)))
        stmts: list[ir.Stmt] = []
        for p in info.params:
            k = self.kinds.get(p.name)
            if k and p.ty == ir.INT:
                stmts.append(ir.ExprStmt(fn.loc, self.in_range(ir.Var(ir.INT, fn.loc, p.name), k)))
        if info.kind == "init":
            self._init_prologue(stmts)
        body = info.body
        if body is not None and body.type == "statements":
            self.block(body, stmts, tail=info.ret != ir.NONE)
        if info.kind == "init":
            self._init_epilogue(stmts)
        fn.body = stmts
        fn.locals = dict(self.env)
        fn.escaped = set(self.escaped)
        self._check_inout(fn)
        return fn

    def _check_inout(self, fn: ir.Function) -> None:
        for s in ir.walk_stmts(fn.body):
            if isinstance(s, ir.Assign) and s.name in self.info.inout and isinstance(self.env.get(s.name), (ir.TList, ir.TDict)):
                raise LowerError(f"replacing the whole of inout '{s.name}' is not modelled (append, index or remove instead)", s.loc.line)

    def in_range(self, e: ir.Expr, kind: str) -> ir.Expr:
        lo, hi = int_range(kind)
        return ir.Builtin(ir.INT, e.loc, "in_range", (e, ir.Lit(ir.INT, e.loc, lo), ir.Lit(ir.INT, e.loc, hi)))

    # -- initializers -------------------------------------------------------

    def _init_prologue(self, out: list[ir.Stmt]) -> None:
        t = self.t
        assert t is not None
        if t.superclass:
            raise self.err(f"initializers of subclasses are not modelled ({t.name} extends {t.superclass})", self.info.node)
        decl = self.file_decl(t)
        self.init_fields = {}
        for fname, fty in decl.fields:
            irn = self.declare(f"self${fname}", fty, None)
            self.init_fields[fname] = irn
            fi = next(f for f in t.fields if f.name == fname)
            k = t.field_kinds.get(fname)
            if k and fty == ir.INT:
                self.kinds[irn] = k
            elif k and isinstance(fty, (ir.TList, ir.TDict)):
                self.elem_kinds[irn] = k
            if fi.default is not None:
                el = ExprLowerer(self)
                v = el.copy_value(el.expr(norm(fi.default), fty, k))
                out.extend(el.pre)
                out.append(ir.Assign(self.loc(fi.default), irn, self.coerce(v, fty)))

    def file_decl(self, t: TypeInfo) -> ir.ClassDecl:
        return self.pj.files[t.path].module.classes[t.name]

    def materialize(self, out: list[ir.Stmt], loc: ir.Loc) -> None:
        """Create the object an initializer builds, from the fields assigned so far."""
        if self.materialized or self.init_fields is None:
            return
        t = self.t
        assert t is not None
        decl = self.file_decl(t)
        args = []
        for fname, fty in decl.fields:
            irn = self.init_fields[fname]
            args.append(ir.Var(fty, loc, irn))
        self.env["self"] = ir.TClass(t.name)
        self.scopes[0]["self"] = "self"
        self.used.add("self")
        out.append(ir.Assign(loc, "self", ir.New(ir.TClass(t.name), loc, t.name, tuple(args))))
        self.materialized = True

    def _init_epilogue(self, out: list[ir.Stmt]) -> None:
        loc = ir.Loc(self.info.node.end_point[0] + 1)
        if out and isinstance(out[-1], ir.Return):
            return
        self.materialize(out, loc)
        t = self.t
        assert t is not None
        out.append(ir.Return(loc, self.coerce(ir.Var(ir.TClass(t.name), loc, "self"), self.info.ret)))

    # -- scopes ---------------------------------------------------------------

    def declare(self, name: str, ty: ir.Type, node: Any, let: bool = False) -> str:
        if name in self.env or name in self.used:
            self.tmp += 1
            ir_name = f"{name}${self.tmp}"
        else:
            ir_name = name
        self.used.add(ir_name)
        self.scopes[-1][name] = ir_name
        self.env[ir_name] = ty
        if let:
            self.lets.add(ir_name)
        return ir_name

    def resolve(self, name: str) -> str | None:
        for sc in reversed(self.scopes):
            if name in sc:
                return sc[name]
        return None

    def push_scope(self) -> None:
        self.scopes.append({})

    def pop_scope(self) -> None:
        self.scopes.pop()

    def coerce(self, e: ir.Expr, ty: ir.Type) -> ir.Expr:
        if e.ty == ty:
            return e
        if isinstance(ty, ir.TOption) and e.ty == ir.NONE:
            return ir.Lit(ty, e.loc, None)
        if isinstance(ty, ir.TOption) and not isinstance(e.ty, ir.TOption) and self.assignable(e.ty, ty.inner):
            return ir.Builtin(ty, e.loc, "some", (e,))
        if isinstance(ty, ir.TList) and isinstance(e, ir.ListLit) and not e.elems:
            return ir.ListLit(ty, e.loc, ())
        if isinstance(ty, ir.TDict) and isinstance(e, ir.Builtin) and e.name == "dict_lit" and not e.args:
            return ir.Builtin(ty, e.loc, "dict_lit", ())
        if isinstance(e.ty, ir.TOpaque) and not isinstance(ty, ir.TOpaque) and ty != ir.NONE:
            return ir.Builtin(ty, e.loc, "from_opaque", (e,))
        if isinstance(ty, ir.TOpaque) and not isinstance(e.ty, ir.TOpaque):
            return ir.Builtin(ty, e.loc, "to_opaque", (e,) if e.ty != ir.NONE else (ir.Lit(ir.INT, e.loc, 0),))
        return e

    def assignable(self, have: ir.Type, want: ir.Type) -> bool:
        """A value of type ``have`` may stand where ``want`` is expected (the
        same type, or a conformer where its protocol is expected)."""
        if have == want:
            return True
        if isinstance(have, ir.TClass) and isinstance(want, ir.TClass):
            t = self.pj.types.get(have.name)
            return t is not None and want.name in t.conforms
        return False

    def is_struct(self, ty: ir.Type) -> bool:
        if not isinstance(ty, ir.TClass):
            return False
        t = self.pj.types.get(ty.name)
        return t is not None and t.kind == "struct"

    def is_class(self, ty: ir.Type) -> bool:
        if not isinstance(ty, ir.TClass):
            return False
        t = self.pj.types.get(ty.name)
        return t is not None and t.kind == "class"

    # -- statements -------------------------------------------------------------

    def block(self, stmts_node: Any, out: list[ir.Stmt], tail: bool = False) -> None:
        """Lower a 'statements' node into ``out``. With ``tail``, a body that
        is a single expression returns it (Swift's implicit return)."""
        self.push_scope()
        try:
            items = [c for c in stmts_node.children if c.is_named and c.type not in EXPR_STMT_SKIP] if stmts_node is not None else []
            prev = _line(stmts_node) - 1 if stmts_node is not None else 0
            if tail and len(items) == 1 and self._is_expression(items[0]):
                s = items[0]
                self._stmt_contracts(prev, _line(s) - 1, out)
                self.value_return(s, out)
                self._stmt_contracts(s.end_point[0] + 1, stmts_node.end_point[0] + 1, out)
                return
            for s in items:
                self._stmt_contracts(prev, _line(s) - 1, out)
                self.stmt(s, out)
                prev = s.end_point[0] + 1
            if stmts_node is not None:
                self._stmt_contracts(prev, stmts_node.end_point[0] + 1, out)
        finally:
            self.pop_scope()

    def _is_expression(self, s: Any) -> bool:
        return s.type not in (
            "property_declaration", "assignment", "while_statement", "repeat_while_statement", "for_statement", "guard_statement",
            "do_statement", "control_transfer_statement", "function_declaration", "class_declaration", "defer_statement", "protocol_declaration",
        )

    def value_return(self, s: Any, out: list[ir.Stmt]) -> None:
        """``s`` is the value of the function (an implicit return)."""
        if s.type in ("if_statement", "switch_statement"):
            target = self.fresh("value", self.info.ret)
            self.valued_statement(s, target, self.info.ret, self.info.ret_kind, out)
            out.append(ir.Return(self.loc(s), ir.Var(self.info.ret, self.loc(s), target)))
            return
        self.stmt_return(norm(s), out, s)

    def stmt_return(self, x: X | None, out: list[ir.Stmt], s: Any) -> None:
        loc = self.loc(s)
        if self.init_fields is not None:
            if x is not None and x.kind == "nil":
                out.append(ir.Return(loc, ir.Lit(self.info.ret, loc, None)))
                return
            if x is not None:
                raise self.err("an initializer returns nothing but nil", s)
            self.materialize(out, loc)
            out.append(ir.Return(loc, self.coerce(ir.Var(self.env["self"], loc, "self"), self.info.ret)))
            return
        ret = self.info.ret
        if x is None:
            out.append(ir.Return(loc, None))
            return
        el = ExprLowerer(self)
        v = el.expr(x, ret, self.info.ret_kind)
        if ret == ir.NONE:
            out.extend(el.pre)
            if not isinstance(v, (ir.Lit, ir.Var)):
                out.append(ir.ExprStmt(loc, v))
            out.append(ir.Return(loc, None))
            return
        if self.is_struct(v.ty) and not (isinstance(v, ir.Var) and v.name in self.env and v.name not in {p.name for p in self.info.params}):
            v = el.copy_value(v)  # the caller gets a value of its own
        out.extend(el.pre)
        v = self.coerce(v, ret)
        if not self.assignable(v.ty, ret) and not isinstance(ret, ir.TOpaque):
            raise self.err(f"returns {v.ty} where {ret} is expected", s)
        out.append(ir.Return(loc, v))

    def stmt(self, s: Any, out: list[ir.Stmt]) -> None:
        was = self.top_level
        try:
            self._stmt(s, out)
        except LowerError as e:
            self.fn.unsupported.append((str(e), ir.Loc(e.line or _line(s))))
            out.append(ir.Unsupported(self.loc(s), str(e)))
        except Unsupported as e:
            self.fn.unsupported.append((str(e), ir.Loc(_line(e.node) or _line(s))))
            out.append(ir.Unsupported(self.loc(s), str(e)))
        finally:
            self.top_level = was

    def nested(self, fn: Any) -> Any:
        was = self.top_level
        self.top_level = False
        try:
            return fn()
        finally:
            self.top_level = was

    def _stmt(self, s: Any, out: list[ir.Stmt]) -> None:
        k = s.type
        loc = self.loc(s)
        if k == "property_declaration":
            self.binding(s, out)
            return
        if k == "assignment":
            self.assignment(s, out)
            return
        if k == "if_statement":
            self.nested(lambda: self.if_stmt(s, out))
            return
        if k == "guard_statement":
            self.guard_stmt(s, out)
            return
        if k in ("while_statement", "repeat_while_statement", "for_statement"):
            self.nested(lambda: self.loop(s, out))
            return
        if k == "switch_statement":
            self.nested(lambda: self.switch(s, out, None, None, None))
            return
        if k == "do_statement":
            self.nested(lambda: self.do_stmt(s, out))
            return
        if k == "control_transfer_statement":
            self.control(s, out)
            return
        if k in ("function_declaration", "class_declaration", "protocol_declaration"):
            raise self.err("nested declarations are not supported", s)
        if k == "defer_statement" or text(s).startswith("defer"):
            raise self.err("defer is not supported yet", s)
        if k == "statement_label" or k == "labeled_statement":
            raise self.err("labelled statements are not supported yet", s)
        x = norm(s)
        el = ExprLowerer(self)
        v = el.expr(x, None)
        out.extend(el.pre)
        if not isinstance(v, (ir.Lit, ir.Var)):
            out.append(ir.ExprStmt(loc, v))

    # let / var

    def binding(self, s: Any, out: list[ir.Stmt]) -> None:
        loc = self.loc(s)
        is_let = any(c.type == "value_binding_pattern" and "let" in text(c) for c in s.children)
        pats = s.children_by_field_name("name")
        vals = s.children_by_field_name("value")
        anns = [c for c in s.children if c.type == "type_annotation"]
        if any(c.type in ("computed_property", "willset_didset_block") for c in s.children) or s.child_by_field_name("computed_value") is not None:
            raise self.err("local computed variables and observers are not supported", s)
        if len(pats) != 1 or len(vals) > 1:
            raise self.err("declare one variable per 'let'/'var' here", s)
        pat = pats[0]
        bid = pat.child_by_field_name("bound_identifier")
        if bid is None:
            if text(pat).strip() == "_" and vals:
                el = ExprLowerer(self)
                v = el.expr(norm(vals[0]), None)
                out.extend(el.pre)
                if not isinstance(v, (ir.Lit, ir.Var)):
                    out.append(ir.ExprStmt(loc, v))
                return
            raise self.err(f"unsupported pattern in a declaration: {text(pat)}", s)
        name = text(bid)
        ann_t, akind = (None, None)
        if anns:
            tn = anns[0].child_by_field_name("name") or next((c for c in anns[0].children if c.is_named), None)
            ann_t, akind = self.pj.stype(tn, self.info.owner, self.info.generics)
        if not vals:
            if ann_t is None:
                raise self.err(f"'{name}' needs a type", s)
            irn = self.declare(name, ann_t, s, let=is_let)
            self._set_kind(irn, ann_t, akind)
            return
        val = vals[0]
        el = ExprLowerer(self)
        if val.type in ("if_statement", "switch_statement"):
            ty = ann_t
            if ty is None:
                raise self.err(f"'{name}' needs a type annotation to hold an if/switch value", s)
            irn = self.declare(name, ty, s, let=is_let)
            self._set_kind(irn, ty, akind)
            self.nested(lambda: self.valued_statement(val, irn, ty, akind, out))
            return
        v = el.copy_value(el.expr(norm(val), ann_t, akind))
        out.extend(el.pre)
        ty = ann_t or v.ty
        if v.ty == ir.NONE and ann_t is None:
            raise self.err(f"'{name}' would hold ()", s)
        if isinstance(ty, ir.TList) and ty.elem == ir.NONE:
            raise self.err(f"the element type of '{name}' is unknown; annotate it", s)
        v = self.coerce(v, ty)
        if not self.assignable(v.ty, ty) and not isinstance(ty, ir.TOpaque):
            raise self.err(f"cannot bind {v.ty} to '{name}' of type {ty}", s)
        irn = self.declare(name, ty, s, let=is_let)
        k = akind or el.kind_of(v) or ("Int" if ty == ir.INT else None)
        if isinstance(ty, (ir.TList, ir.TDict)):
            k = akind or el.kind_of_elems(v)
        self._set_kind(irn, ty, k)
        out.append(ir.Assign(loc, irn, v))

    def _set_kind(self, irn: str, ty: ir.Type, k: str | None) -> None:
        if not k:
            return
        if isinstance(ty, (ir.TList, ir.TDict)):
            self.elem_kinds[irn] = k
        elif ty == ir.INT or isinstance(ty, ir.TOption):
            self.kinds[irn] = k

    # assignment

    def assignment(self, s: Any, out: list[ir.Stmt]) -> None:
        target = s.child_by_field_name("target")
        op = text(s.child_by_field_name("operator"))
        val = s.child_by_field_name("result")
        tx = norm(named(target)[0]) if target is not None and named(target) else None
        if tx is None:
            raise self.err("unsupported assignment", s)
        loc = self.loc(s)
        el = ExprLowerer(self)
        if tx.kind == "name" and tx.id == "_":
            v = el.expr(norm(val), None)
            out.extend(el.pre)
            if not isinstance(v, (ir.Lit, ir.Var)):
                out.append(ir.ExprStmt(loc, v))
            return
        if op == "=":
            tty, tkind = el.lvalue_type(tx)
            if val.type in ("if_statement", "switch_statement"):
                t = self.fresh("value", tty)
                self.nested(lambda: self.valued_statement(val, t, tty, tkind, out))
                v: ir.Expr = ir.Var(tty, loc, t)
            else:
                v = el.copy_value(el.expr(norm(val), tty, tkind))
            el.store(tx, v, loc)
            out.extend(el.pre)
            return
        bop = op[:-1]
        cur = el.expr(tx, None)
        rhs = X("binop", s, op=bop, l=_Fixed(cur, tx), r=norm(val))
        v = el.expr(rhs, cur.ty, el.kind_of(cur))
        el.store(tx, v, loc)
        out.extend(el.pre)

    # conditions (if / guard / while)

    def conditions(self, s: Any) -> list[tuple[str, Any]]:
        """The ','-separated conditions of an if/guard/while: ('bool', X),
        ('let', (name, X, is_var)), ('case', (pattern text, X, node))."""
        stop = {"{", "else", "statements"}
        groups: list[list[Any]] = [[]]
        for i, c in enumerate(s.children):
            if i == 0:
                continue  # the keyword
            if c.type in stop or c.type == "else":
                break
            if c.type == ",":
                groups.append([])
                continue
            groups[-1].append((s.field_name_for_child(i), c))
        out: list[tuple[str, Any]] = []
        for g in groups:
            if not g:
                continue
            first = g[0][1]
            if first.type == "value_binding_pattern":
                bid = next((c for f, c in g if f == "bound_identifier"), None)
                rest = [c for f, c in g[1:] if f == "condition" and c.type != "="]
                if bid is None and rest and any(c.type == "wildcard_pattern" or text(c) == "_" for _, c in g[1:]):
                    out.append(("let", ("_", norm(rest[-1]), False)))
                    continue
                if bid is None:
                    raise self.err("unsupported optional binding", first)
                val = norm(rest[-1]) if rest else X("name", bid, id=text(bid))
                out.append(("let", (text(bid), val, "var" in text(first))))
                continue
            if first.type == "case" or text(first) == "case":
                eq = next(i for i, (f, c) in enumerate(g) if c.type == "=")
                pat_nodes = [c for _, c in g[1:eq]]
                val = norm(g[-1][1]) if eq + 1 < len(g) else None
                if val is None or eq + 2 != len(g):
                    raise self.err("unsupported 'case' condition", first)
                pat_src = self.file.source.encode("utf8")[pat_nodes[0].start_byte : pat_nodes[-1].end_byte].decode("utf8")
                out.append(("case", (pat_src, val, pat_nodes[0])))
                continue
            if len(g) != 1:
                raise self.err("unsupported condition", first)
            out.append(("bool", norm(first)))
        return out

    def cond_chain(self, conds: list[tuple[str, Any]], on_success: Any, loc: ir.Loc, node: Any) -> list[ir.Stmt]:
        """Evaluate the conditions in order; run ``on_success(out)`` (with the
        bindings in scope) only if all hold."""
        if not conds:
            body: list[ir.Stmt] = []
            on_success(body)
            return body
        kind, c = conds[0]
        out: list[ir.Stmt] = []
        if kind == "bool":
            el = ExprLowerer(self)
            v = el.expr(c, ir.BOOL)
            if v.ty != ir.BOOL:
                raise self.err("a condition must be a Bool", node)
            out.extend(el.pre)
            out.append(ir.If(loc, v, tuple(self.cond_chain(conds[1:], on_success, loc, node)), ()))
            return out
        if kind == "let":
            name, val, is_var = c
            el = ExprLowerer(self)
            v = el.expr(val, None)
            out.extend(el.pre)
            if not isinstance(v.ty, ir.TOption):
                if isinstance(v.ty, ir.TOpaque):
                    raise self.err(f"'{name}' binds an unchecked optional; its value is not modelled", node)
                raise self.err(f"'if let {name}' needs an optional, not {v.ty}", node)
            if not isinstance(v, ir.Var):
                t = self.fresh("opt", v.ty)
                out.append(ir.Assign(loc, t, v))
                v = ir.Var(v.ty, loc, t)
            k = el.kind_of(v)
            inner: list[ir.Stmt] = []
            if name != "_":
                irn = self.declare(name, v.ty.inner, node, let=not is_var)
                if k:
                    self.kinds[irn] = k
                u = ir.Builtin(v.ty.inner, loc, "unwrap", (v,))
                inner.append(ir.Assign(loc, irn, self._copy_now(u, inner, loc)))
                if k and v.ty.inner == ir.INT:
                    inner.append(ir.ExprStmt(loc, self.in_range(ir.Var(ir.INT, loc, irn), k)))
            inner.extend(self.cond_chain(conds[1:], on_success, loc, node))
            out.append(ir.If(loc, ir.Unary(ir.BOOL, loc, "not", ir.Builtin(ir.BOOL, loc, "is_none", (v,))), tuple(inner), ()))
            return out
        pat_src, val, pnode = c
        el = ExprLowerer(self)
        scrut = el.hoist_var(el.expr(val, None))
        out.extend(el.pre)
        pat = self.parse_pattern(pat_src, pnode)
        cond, binds = el.pattern(pat, scrut)
        inner = []
        for b, e, let in binds:
            irn = self.declare(b, e.ty, pnode, let=let)
            inner.append(ir.Assign(loc, irn, self._copy_now(e, inner, loc)))
        inner.extend(self.cond_chain(conds[1:], on_success, loc, node))
        out.append(ir.If(loc, cond, tuple(inner), ()))
        return out

    def _copy_now(self, e: ir.Expr, out: list[ir.Stmt], loc: ir.Loc) -> ir.Expr:
        el = ExprLowerer(self)
        v = el.copy_value(e)
        out.extend(el.pre)
        return v

    def parse_pattern(self, src: str, at: Any) -> Any:
        wrapped = f"switch __telic {{\ncase {src}: break\n}}"
        from .swift_syntax import parser

        tree = parser().parse(wrapped.encode("utf8"))
        if tree.root_node.has_error:
            raise self.err(f"cannot parse the pattern '{src}'", at)
        sw = tree.root_node.children[0]
        entry = next(c for c in sw.children if c.type == "switch_entry")
        sp = next(c for c in entry.children if c.type == "switch_pattern")
        return _Shifted(sp, at)

    def if_stmt(self, s: Any, out: list[ir.Stmt]) -> None:
        loc = self.loc(s)
        conds = self.conditions(s)
        bodies = [c for c in s.children if c.type == "statements"]
        then_n = None
        else_n = None
        seen_else = False
        for c in s.children:
            if c.type == "else":
                seen_else = True
                continue
            if c.type == "statements" and not seen_else and then_n is None:
                then_n = c
            elif seen_else and c.type in ("statements", "if_statement"):
                else_n = c
        del bodies
        simple = all(k == "bool" for k, _ in conds)
        if simple and len(conds) == 1:
            el = ExprLowerer(self)
            c = el.expr(conds[0][1], ir.BOOL)
            if c.ty != ir.BOOL:
                raise self.err("a condition must be a Bool", s)
            out.extend(el.pre)
            t: list[ir.Stmt] = []
            self.push_scope()
            try:
                if then_n is not None:
                    self.block(then_n, t)
            finally:
                self.pop_scope()
            e: list[ir.Stmt] = []
            if else_n is not None:
                if else_n.type == "if_statement":
                    self.stmt(else_n, e)
                else:
                    self.block(else_n, e)
            out.append(ir.If(loc, c, tuple(t), tuple(e)))
            return
        ok = self.fresh("ok", ir.BOOL)
        out.append(ir.Assign(loc, ok, ir.Lit(ir.BOOL, loc, False)))

        def success(body: list[ir.Stmt]) -> None:
            body.append(ir.Assign(loc, ok, ir.Lit(ir.BOOL, loc, True)))
            if then_n is not None:
                self.block(then_n, body)

        self.push_scope()
        try:
            out.extend(self.cond_chain(conds, success, loc, s))
        finally:
            self.pop_scope()
        if else_n is not None:
            e = []
            if else_n.type == "if_statement":
                self.stmt(else_n, e)
            else:
                self.block(else_n, e)
            out.append(ir.If(loc, ir.Unary(ir.BOOL, loc, "not", ir.Var(ir.BOOL, loc, ok)), tuple(e), ()))

    def guard_stmt(self, s: Any, out: list[ir.Stmt]) -> None:
        loc = self.loc(s)
        conds = self.conditions(s)
        else_n = next((c for c in s.children if c.type == "statements"), None)

        def otherwise() -> list[ir.Stmt]:
            e: list[ir.Stmt] = []
            self.nested(lambda: self.block(else_n, e) if else_n is not None else None)
            if not _exits(e):
                raise self.err("the else of a guard must leave the scope (return, throw, break, continue or a trap)", s)
            return e

        # bindings stay in scope after the guard: declared in the current scope
        self.fail_chain(conds, otherwise, loc, s, out)

    def fail_chain(self, conds: list[tuple[str, Any]], otherwise: Any, loc: ir.Loc, node: Any, out: list[ir.Stmt]) -> None:
        """Each condition in turn: when it fails, run ``otherwise()`` (which
        leaves); past it, its bindings hold."""
        for kind, c in conds:
            if kind == "bool":
                el = ExprLowerer(self)
                v = el.expr(c, ir.BOOL)
                if v.ty != ir.BOOL:
                    raise self.err("a condition must be a Bool", node)
                out.extend(el.pre)
                out.append(ir.If(loc, ir.Unary(ir.BOOL, loc, "not", v), tuple(otherwise()), ()))
                continue
            if kind == "let":
                name, val, is_var = c
                el = ExprLowerer(self)
                v = el.expr(val, None)
                out.extend(el.pre)
                if not isinstance(v.ty, ir.TOption):
                    raise self.err(f"'let {name}' needs an optional, not {v.ty}", node)
                if not isinstance(v, ir.Var):
                    t = self.fresh("opt", v.ty)
                    out.append(ir.Assign(loc, t, v))
                    v = ir.Var(v.ty, loc, t)
                k = el.kind_of(v)
                out.append(ir.If(loc, ir.Builtin(ir.BOOL, loc, "is_none", (v,)), tuple(otherwise()), ()))
                if name == "_":
                    continue
                irn = self.declare(name, v.ty.inner, node, let=not is_var)
                if k:
                    self.kinds[irn] = k
                out.append(ir.Assign(loc, irn, self._copy_now(ir.Builtin(v.ty.inner, loc, "unwrap", (v,)), out, loc)))
                if k and v.ty.inner == ir.INT:
                    out.append(ir.ExprStmt(loc, self.in_range(ir.Var(ir.INT, loc, irn), k)))
                continue
            pat_src, val, pnode = c
            el = ExprLowerer(self)
            scrut = el.hoist_var(el.expr(val, None))
            out.extend(el.pre)
            cond, binds = el.pattern(self.parse_pattern(pat_src, pnode), scrut)
            out.append(ir.If(loc, ir.Unary(ir.BOOL, loc, "not", cond), tuple(otherwise()), ()))
            for b, e, let in binds:
                irn = self.declare(b, e.ty, pnode, let=let)
                out.append(ir.Assign(loc, irn, self._copy_now(e, out, loc)))

    # loops

    def loop(self, s: Any, out: list[ir.Stmt]) -> None:
        loc = self.loc(s)
        body = next((c for c in s.children if c.type == "statements"), None)
        cls = self._loop_contracts(s, body)
        self.loop_depth += 1
        try:
            if s.type == "while_statement":
                invs, dec = self._loop_clauses(cls)
                conds = self.conditions(s)
                if len(conds) == 1 and conds[0][0] == "bool":
                    el = ExprLowerer(self)
                    c = el.expr(conds[0][1], ir.BOOL)
                    if not el.pre:
                        b: list[ir.Stmt] = []
                        self._loop_body(body, b)
                        out.append(ir.While(loc, c, invs, dec, tuple(b)))
                        return
                b = []
                self.push_scope()
                try:
                    self.fail_chain(conds, lambda: [ir.Break(loc)], loc, s, b)
                    self._loop_body(body, b)
                finally:
                    self.pop_scope()
                out.append(ir.While(loc, ir.Lit(ir.BOOL, loc, True), invs, dec, tuple(b)))
                return
            if s.type == "repeat_while_statement":
                invs, dec = self._loop_clauses(cls)
                if body is not None and _has_continue(body):
                    raise self.err("'continue' in repeat-while is not supported yet", s)
                cond_n = s.child_by_field_name("condition")
                b = []
                self._loop_body(body, b)
                el = ExprLowerer(self)
                c = el.expr(norm(cond_n), ir.BOOL)
                b.extend(el.pre)
                b.append(ir.If(loc, ir.Unary(ir.BOOL, loc, "not", c), (ir.Break(loc),), ()))
                out.append(ir.While(loc, ir.Lit(ir.BOOL, loc, True), invs, dec, tuple(b)))
                return
            self.for_loop(s, body, cls, out, loc)
        finally:
            self.loop_depth -= 1

    def _loop_body(self, body: Any, out: list[ir.Stmt]) -> None:
        start = len(out)
        before = set(self.env)
        if body is not None:
            self.block(body, out)
        loc = self.loc(body) if body is not None else ir.NOLOC
        facts = [ir.ExprStmt(loc, self.in_range(ir.Var(ir.INT, loc, n), self.kinds[n])) for n in sorted(ir.assigned_names(out[start:])) if n in before and n in self.kinds and self.env.get(n) == ir.INT]
        out[start:start] = facts

    def for_loop(self, s: Any, body: Any, cls: list[ContractLine], out: list[ir.Stmt], loc: ir.Loc) -> None:
        item = s.child_by_field_name("item")
        coll = s.child_by_field_name("collection")
        where = next((c for c in s.children if c.type == "where_clause"), None)
        if item is None or coll is None:
            raise self.err("unsupported for loop", s)
        if any(cl.keyword == "decreases" for cl in cls):
            raise self.err("a for-in loop over a range or an array terminates by construction; remove '@decreases'", s)
        clauses = lambda: self._loop_clauses(cls)[0]  # noqa: E731 - lowered once the loop variables exist
        cx = norm(coll)
        while cx.kind == "paren":
            cx = cx.e
        names = _pattern_names(item)
        if names is None:
            raise self.err(f"unsupported loop pattern '{text(item)}'", item)

        def body_with_where(b: list[ir.Stmt]) -> None:
            if where is None:
                self._loop_body(body, b)
                return
            wx = norm(next(c for c in where.children if c.is_named and c.type != "where_keyword"))
            el = ExprLowerer(self)
            w = el.expr(wx, ir.BOOL)
            b.extend(el.pre)
            inner: list[ir.Stmt] = []
            self._loop_body(body, inner)
            b.append(ir.If(loc, w, tuple(inner), ()))

        # for i in a..<b / a...b
        if cx.kind == "range" and cx.lo is not None and cx.hi is not None:
            if len(names) != 1:
                raise self.err("a range loop binds one name", item)
            el = ExprLowerer(self)
            lo = el.expr(cx.lo, ir.INT)
            hi = el.expr(cx.hi, ir.INT)
            out.extend(el.pre)
            if lo.ty != ir.INT or hi.ty != ir.INT:
                raise self.err("range bounds must be integers", coll)
            k = el.kind_of(lo) or el.kind_of(hi) or "Int"
            if cx.op == "...":
                # a...b traps when b < a; a..<b when b < a too
                out.append(ir.AssertStmt(loc, ir.Clause("assert", ir.Binary(ir.BOOL, loc, "le", lo, hi), loc, "range lower bound <= upper bound"), native=True))
                hi = ir.Binary(ir.INT, hi.loc, "add", hi, ir.Lit(ir.INT, hi.loc, 1))
            else:
                out.append(ir.AssertStmt(loc, ir.Clause("assert", ir.Binary(ir.BOOL, loc, "le", lo, hi), loc, "range lower bound <= upper bound"), native=True))
            self.push_scope()
            try:
                v = self.declare(names[0] if names[0] != "_" else "_i", ir.INT, item, let=True)
                self.kinds[v] = k
                invs = clauses()
                b: list[ir.Stmt] = []
                body_with_where(b)
            finally:
                self.pop_scope()
            out.append(ir.ForRange(loc, v, lo, hi, invs, tuple(b)))
            return
        # for i in stride(from: a, to: b, by: step)
        if cx.kind == "call" and cx.callee.kind == "name" and cx.callee.id == "stride":
            self._stride(cx, names, item, clauses, body_with_where, out, loc)
            return
        # for i in (a..<b).reversed()
        if cx.kind == "call" and cx.callee.kind == "member" and cx.callee.name == "reversed" and not cx.args:
            base = cx.callee.base
            while base.kind == "paren":
                base = base.e
            if base.kind == "range" and base.lo is not None and base.hi is not None and len(names) == 1:
                self._countdown(base, names[0], item, clauses, body_with_where, out, loc)
                return
        # for x in xs / for (i, x) in xs.enumerated() / for i in xs.indices
        enum_idx = False
        seq_x = cx
        if cx.kind == "call" and cx.callee.kind == "member" and cx.callee.name == "enumerated" and not cx.args:
            enum_idx = True
            seq_x = cx.callee.base
        if cx.kind == "member" and cx.name == "indices":
            el = ExprLowerer(self)
            seq = el.expr(cx.base, None)
            out.extend(el.pre)
            if not isinstance(seq.ty, ir.TList) or len(names) != 1:
                raise self.err(".indices of a non-array", coll)
            self.push_scope()
            try:
                v = self.declare(names[0], ir.INT, item, let=True)
                self.kinds[v] = "Int"
                invs = clauses()
                b = []
                body_with_where(b)
            finally:
                self.pop_scope()
            out.append(ir.ForRange(loc, v, ir.Lit(ir.INT, loc, 0), ir.Builtin(ir.INT, loc, "len", (seq,)), invs, tuple(b)))
            return
        el = ExprLowerer(self)
        seq = el.expr(seq_x, None)
        out.extend(el.pre)
        if isinstance(seq.ty, ir.TDict):
            raise self.err("iterating a Dictionary is not modelled (its order is unspecified)", coll)
        if isinstance(seq.ty, ir.TOpaque):
            seq = ir.Builtin(ir.TList(ir.TOpaque("")), seq.loc, "from_opaque", (seq,))
        if not isinstance(seq.ty, ir.TList):
            raise self.err(f"for-in needs an array or a range here, not {seq.ty}", coll)
        ek = el.kind_of_elems(seq)
        self.push_scope()
        try:
            if enum_idx:
                if len(names) != 2:
                    raise self.err("use 'for (i, x) in xs.enumerated()'", item)
                iname = self.declare(names[0] if names[0] != "_" else "_i", ir.INT, item, let=True)
                self.kinds[iname] = "Int"
                ename_src = names[1]
                idx, visible = iname, True
            else:
                if len(names) != 1:
                    raise self.err("for-in over an array binds one name", item)
                ename_src = names[0]
                idx, visible = self.fresh("i", ir.INT), False
            ename = self.declare(ename_src if ename_src != "_" else "_x", seq.ty.elem, item, let=True)
            if ek:
                self.kinds[ename] = ek
            invs = clauses()
            b = []
            if ek and seq.ty.elem == ir.INT:
                b.append(ir.ExprStmt(loc, self.in_range(ir.Var(ir.INT, loc, ename), ek)))
            body_with_where(b)
        finally:
            self.pop_scope()
        out.append(ir.ForEach(loc, ename, idx, seq, invs, tuple(b), idx_visible=visible))

    def _stride(self, cx: X, names: list[str], item: Any, clauses: Any, body_fn: Any, out: list[ir.Stmt], loc: ir.Loc) -> None:
        """``for i in stride(from: a, to: b, by: step)``: invariants see ``i``
        as the value of the next iteration (so it is past the end after the
        last one), as for a range loop."""
        args = dict((lbl, a) for lbl, a in cx.args)
        if set(args) not in ({"from", "to", "by"}, {"from", "through", "by"}) or len(names) != 1:
            raise self.err("stride(from:to:by:) / stride(from:through:by:) with one loop variable", item)
        step_x = args["by"]
        neg = step_x.kind == "prefix" and step_x.op == "-" and step_x.e.kind == "int"
        if not (step_x.kind == "int" or neg):
            raise self.err("stride needs a literal step", item)
        step = int((step_x.e if neg else step_x).text.replace("_", ""), 0) * (-1 if neg else 1)
        if step == 0:
            raise self.err("stride by 0 traps", item)
        el = ExprLowerer(self)
        lo = el.hoist_var(el.expr(args["from"], ir.INT))
        end = el.hoist_var(el.expr(args.get("to") or args["through"], ir.INT))
        out.extend(el.pre)
        inclusive = "through" in args
        self.push_scope()
        try:
            v = self.declare(names[0] if names[0] != "_" else "_i", ir.INT, item)
            out.append(ir.Assign(loc, v, lo))
            kv = ir.Var(ir.INT, loc, v)
            invs = clauses()
            b: list[ir.Stmt] = []
            body_fn(b)
        finally:
            self.pop_scope()
        op = ("le" if inclusive else "lt") if step > 0 else ("ge" if inclusive else "gt")
        cond = ir.Binary(ir.BOOL, loc, op, kv, end)
        measure = ir.Binary(ir.INT, loc, "sub", end, kv) if step > 0 else ir.Binary(ir.INT, loc, "sub", kv, end)
        dec = ir.Clause("decreases", ir.Binary(ir.INT, loc, "add", measure, ir.Lit(ir.INT, loc, abs(step))), loc, "end - i", inferred=True)
        # (the stride stops before stepping past Int's range)
        step_s = (ir.Assign(loc, v, ir.Binary(ir.INT, loc, "add", kv, ir.Lit(ir.INT, loc, step))),)
        out.append(ir.While(loc, cond, invs, dec, tuple(b), step=step_s))

    def _countdown(self, rng: X, name: str, item: Any, clauses: Any, body_fn: Any, out: list[ir.Stmt], loc: ir.Loc) -> None:
        """``for i in (a..<b).reversed()``: invariants see ``i`` as the value of
        the last iteration (``b`` before the first one, ``a`` after the last)."""
        el = ExprLowerer(self)
        lo = el.hoist_var(el.expr(rng.lo, ir.INT))
        hi = el.hoist_var(el.expr(rng.hi, ir.INT))
        out.extend(el.pre)
        out.append(ir.AssertStmt(loc, ir.Clause("assert", ir.Binary(ir.BOOL, loc, "le", lo, hi), loc, "range lower bound <= upper bound"), native=True))
        if rng.op == "...":
            hi = ir.Binary(ir.INT, loc, "add", hi, ir.Lit(ir.INT, loc, 1))
        self.push_scope()
        try:
            v = self.declare(name if name != "_" else "_i", ir.INT, item)
            out.append(ir.Assign(loc, v, hi))
            kv = ir.Var(ir.INT, loc, v)
            invs = clauses()
            b: list[ir.Stmt] = [ir.Assign(loc, v, ir.Binary(ir.INT, loc, "sub", kv, ir.Lit(ir.INT, loc, 1)))]
            body_fn(b)
        finally:
            self.pop_scope()
        dec = ir.Clause("decreases", ir.Binary(ir.INT, loc, "sub", kv, lo), loc, "i - lo", inferred=True)
        out.append(ir.While(loc, ir.Binary(ir.BOOL, loc, "lt", lo, kv), invs, dec, tuple(b)))

    # switch

    def switch(self, s: Any, out: list[ir.Stmt], target: str | None, ty: ir.Type | None, kind: str | None) -> None:
        loc = self.loc(s)
        scrut_n = s.child_by_field_name("expr")
        el = ExprLowerer(self)
        scrut = el.hoist_var(el.expr(norm(scrut_n), None))
        out.extend(el.pre)
        entries = [c for c in s.children if c.type == "switch_entry"]
        arms: list[tuple[ir.Expr, list[ir.Stmt]]] = []
        self.switch_depth.append(self.loop_depth)
        try:
            for i, entry in enumerate(entries):
                pats = [c for c in entry.children if c.type == "switch_pattern"]
                is_default = any(c.type == "default_keyword" for c in entry.children)
                where_i = next((j for j, c in enumerate(entry.children) if c.type == "where_keyword"), None)
                guard_n = entry.children[where_i + 1] if where_i is not None else None
                body_n = next((c for c in entry.children if c.type == "statements"), None)
                if body_n is not None and any(c.type == "control_transfer_statement" and text(c).startswith("fallthrough") for c in body_n.children):
                    raise self.err("fallthrough is not supported", entry)
                self.push_scope()
                try:
                    pre: list[ir.Stmt] = []
                    if is_default:
                        cond: ir.Expr = ir.Lit(ir.BOOL, loc, True)
                    else:
                        conds = []
                        binds_all: list[tuple[str, ir.Expr, bool]] | None = None
                        for p in pats:
                            pel = ExprLowerer(self)
                            c, binds = pel.pattern(p, scrut)
                            if pel.pre:
                                raise self.err("patterns with effects are not supported", p)
                            conds.append(c)
                            if binds and len(pats) > 1:
                                raise self.err("several patterns in one case that bind names are not supported", entry)
                            binds_all = binds
                        cond = conds[0]
                        for c in conds[1:]:
                            cond = ir.Binary(ir.BOOL, loc, "or", cond, c)
                        for b, e, let in binds_all or []:
                            irn = self.declare(b, e.ty, entry, let=let)
                            pre.append(ir.Assign(loc, irn, e))
                    if guard_n is not None:
                        gel = ExprLowerer(self)
                        g = gel.expr(norm(guard_n), ir.BOOL)
                        if gel.pre:
                            raise self.err("a 'where' with effects is not supported", guard_n)
                        if pre:
                            # the guard reads the bindings: evaluate it on the bound values
                            g = _subst(g, {a.name: a.value for a in pre if isinstance(a, ir.Assign)})
                        cond = g if isinstance(cond, ir.Lit) and cond.value is True else ir.Binary(ir.BOOL, loc, "and", cond, g)
                    body: list[ir.Stmt] = list(pre)
                    if body_n is not None:
                        items = [c for c in body_n.children if c.is_named and c.type not in EXPR_STMT_SKIP]
                        if items and items[-1].type == "control_transfer_statement" and text(items[-1]).strip() == "break":
                            items = items[:-1]  # 'break' ends the case; nothing to do
                            if not items:
                                arms.append((cond, body))
                                continue
                        if target is not None and len(items) == 1 and self._is_expression(items[0]):
                            if items[0].type in ("if_statement", "switch_statement"):
                                self.valued_statement(items[0], target, ty, kind, body)
                            else:
                                vel = ExprLowerer(self)
                                v = vel.copy_value(vel.expr(norm(items[0]), ty, kind))
                                body.extend(vel.pre)
                                body.append(ir.Assign(loc, target, self.coerce(v, ty)))  # type: ignore[arg-type]
                        else:
                            self.push_scope()
                            try:
                                prev = _line(body_n) - 1
                                for it in items:
                                    self._stmt_contracts(prev, _line(it) - 1, body)
                                    self.stmt(it, body)
                                    prev = it.end_point[0] + 1
                            finally:
                                self.pop_scope()
                    arms.append((cond, body))
                finally:
                    self.pop_scope()
        finally:
            self.switch_depth.pop()
        if not arms:
            return
        # Swift checks exhaustiveness: when no earlier case matched, the last one does
        chain: tuple[ir.Stmt, ...] = tuple(arms[-1][1])
        for cond, body in reversed(arms[:-1]):
            chain = (ir.If(loc, cond, tuple(body), chain),)
        out.extend(chain)

    def valued_statement(self, s: Any, target: str, ty: ir.Type | None, kind: str | None, out: list[ir.Stmt]) -> None:
        """An if or switch used as a value: each branch assigns ``target``."""
        if s.type == "switch_statement":
            self.switch(s, out, target, ty, kind)
            return
        loc = self.loc(s)
        conds = self.conditions(s)
        if len(conds) != 1 or conds[0][0] != "bool":
            raise self.err("if-expressions with bindings are not supported", s)
        el = ExprLowerer(self)
        c = el.expr(conds[0][1], ir.BOOL)
        out.extend(el.pre)
        branches = []
        seen_else = False
        for ch in s.children:
            if ch.type == "else":
                seen_else = True
            elif ch.type == "statements" or seen_else and ch.type == "if_statement":
                branches.append(ch)
        if len(branches) != 2:
            raise self.err("an if-expression needs an else", s)

        def arm(n: Any) -> list[ir.Stmt]:
            b: list[ir.Stmt] = []
            if n.type == "if_statement":
                self.valued_statement(n, target, ty, kind, b)
                return b
            items = [x for x in n.children if x.is_named and x.type not in EXPR_STMT_SKIP]
            if len(items) != 1:
                raise self.err("each branch of an if-expression is one expression", n)
            if items[0].type in ("if_statement", "switch_statement"):
                self.valued_statement(items[0], target, ty, kind, b)
                return b
            vel = ExprLowerer(self)
            v = vel.copy_value(vel.expr(norm(items[0]), ty, kind))
            b.extend(vel.pre)
            b.append(ir.Assign(loc, target, self.coerce(v, ty) if ty is not None else v))
            return b

        out.append(ir.If(loc, c, tuple(arm(branches[0])), tuple(arm(branches[1]))))

    # do / catch

    def do_stmt(self, s: Any, out: list[ir.Stmt]) -> None:
        """do/catch: an error thrown in the body skips the rest of it and runs
        a catch clause from the state at the throw."""
        loc = self.loc(s)
        body_n = next((c for c in s.children if c.type == "statements"), None)
        catches = [c for c in s.children if c.type == "catch_block"]
        body: list[ir.Stmt] = []
        if catches:
            self.do_depth += 1
        try:
            if body_n is not None:
                self.block(body_n, body)
        finally:
            if catches:
                self.do_depth -= 1
        if not catches:
            out.extend(body)
            return
        flag = self.fresh("thrown", ir.BOOL)
        out.append(ir.Assign(loc, flag, ir.Lit(ir.BOOL, loc, False)))
        out.extend(_catchify(body, flag, False, loc))
        handlers: list[list[ir.Stmt]] = []
        exhaustive = False
        for c in catches:
            pat = c.child_by_field_name("error")
            if pat is None or re.fullmatch(r"\s*let\s+\w+\s*", text(pat)):
                exhaustive = True
            self.push_scope()
            try:
                h: list[ir.Stmt] = []
                names = ["error"] if pat is None else re.findall(r"\b(?:let|var)\s+(\w+)", text(pat))
                for nm in names:
                    irn = self.declare(nm, ir.TOpaque("Error"), c, let=True)
                    h.append(ir.Assign(loc, irn, ir.Extern(ir.TOpaque("Error"), loc, "caught exception", ())))
                hb = next((x for x in c.children if x.type == "statements"), None)
                if hb is not None:
                    self.block(hb, h)
                handlers.append(h)
            finally:
                self.pop_scope()
            if exhaustive:
                break
        # which clause matches the error is not modelled: any may
        chain: tuple[ir.Stmt, ...] = tuple(handlers[-1]) if exhaustive else (ir.Raise(loc, "an error no catch clause matches", caught=self.do_depth > 0),)
        rest = handlers[:-1] if exhaustive else handlers
        for i, h in reversed(list(enumerate(rest))):
            choice = ir.Builtin(ir.BOOL, loc, "opaque_op", (ir.Lit(ir.STR, loc, "catch clause matches"), ir.Lit(ir.INT, loc, self.tmp), ir.Lit(ir.INT, loc, i)))
            chain = (ir.If(loc, choice, tuple(h), chain),)
        out.append(ir.If(loc, ir.Var(ir.BOOL, loc, flag), chain, ()))

    # return / break / continue / throw

    def control(self, s: Any, out: list[ir.Stmt]) -> None:
        loc = self.loc(s)
        t = text(s).strip()
        kids = [c for c in named(s) if c.type != "throw_keyword"]
        if t.startswith("return"):
            val = s.child_by_field_name("result") or (kids[0] if kids else None)
            self.stmt_return(norm(val) if val is not None else None, out, s)
            return
        if t.startswith("throw"):
            what = text(kids[0]) if kids else "an error"
            if kids:
                el = ExprLowerer(self)
                v = el.expr(norm(kids[0]), None)
                out.extend(el.pre)
                if not isinstance(v, (ir.Lit, ir.Var)) and not (isinstance(v, ir.Builtin) and v.name in ("opaque_op",)):
                    out.append(ir.ExprStmt(loc, v))
            out.append(ir.Raise(loc, what[:60], caught=self.do_depth > 0))
            return
        if t.startswith("break"):
            if len(t.split()) > 1:
                raise self.err("labelled break is not supported yet", s)
            if self.switch_depth and self.switch_depth[-1] == self.loop_depth:
                raise self.err("'break' inside a switch case is only supported as the case's only statement", s)
            out.append(ir.Break(loc))
            return
        if t.startswith("continue"):
            if len(t.split()) > 1:
                raise self.err("labelled continue is not supported yet", s)
            out.append(ir.Continue(loc))
            return
        if t.startswith("fallthrough"):
            raise self.err("fallthrough is not supported", s)
        raise self.err(f"unsupported statement '{t[:30]}'", s)


def _has_throw(stmts: Any) -> bool:
    return any(isinstance(s, ir.Raise) and s.caught for s in ir.walk_stmts(stmts))


def _catchify(stmts: list[ir.Stmt] | tuple, flag: str, in_loop: bool, loc: ir.Loc) -> list[ir.Stmt]:
    """Turn the throws of a do body into setting ``flag`` and skipping the
    rest of the body: out of loops by 'break', past the rest of a block by
    guarding it with the flag."""
    stmts = list(stmts)
    fv = ir.Var(ir.BOOL, loc, flag)
    not_thrown = ir.Unary(ir.BOOL, loc, "not", fv)
    for i, s in enumerate(stmts):
        if isinstance(s, ir.Raise) and s.caught:
            return stmts[:i] + [ir.Assign(s.loc, flag, ir.Lit(ir.BOOL, s.loc, True))] + ([ir.Break(s.loc)] if in_loop else [])
        if not _has_throw([s]):
            continue
        rest = stmts[i + 1 :]
        if isinstance(s, ir.If):
            s2: ir.Stmt = ir.If(s.loc, s.cond, tuple(_catchify(s.then, flag, in_loop, loc)), tuple(_catchify(s.orelse, flag, in_loop, loc)))
        elif isinstance(s, (ir.While, ir.ForRange, ir.ForEach)):
            inv = ir.Clause("invariant", not_thrown, s.loc, "nothing thrown yet", inferred=True)
            s2 = dataclasses.replace(s, body=tuple(_catchify(s.body, flag, True, loc)), invariants=tuple(s.invariants) + (inv,))
        else:
            raise LowerError("a throw inside this construct is not supported in a do body", s.loc.line)
        if in_loop:
            return stmts[:i] + [s2, ir.If(loc, fv, (ir.Break(loc),), tuple(_catchify(rest, flag, True, loc)))]
        return stmts[:i] + [s2] + ([ir.If(loc, not_thrown, tuple(_catchify(rest, flag, False, loc)), ())] if rest else [])
    return stmts


def _pattern_names(item: Any) -> list[str] | None:
    """Names bound by a for-loop pattern: 'x', '(i, x)', '_'."""
    t = text(item).strip()
    if re.fullmatch(r"(?:let\s+|var\s+)?[A-Za-z_]\w*", t):
        return [t.split()[-1]]
    m = re.fullmatch(r"\(\s*([A-Za-z_]\w*)\s*,\s*([A-Za-z_]\w*)\s*\)", t)
    if m:
        return [m.group(1), m.group(2)]
    return None


def _exits(stmts: list[ir.Stmt]) -> bool:
    if not stmts:
        return False
    last = stmts[-1]
    if isinstance(last, (ir.Return, ir.Break, ir.Continue, ir.Raise, ir.Unsupported)):
        return True
    if isinstance(last, ir.AssertStmt) and isinstance(last.clause.expr, ir.Lit) and last.clause.expr.value is False:
        return True
    if isinstance(last, ir.If):
        return _exits(list(last.then)) and _exits(list(last.orelse))
    if isinstance(last, ir.Try):
        return _exits(list(last.body)) and all(_exits(list(h)) for h in last.handlers)
    return False


def _has_continue(n: Any) -> bool:
    if n.type == "control_transfer_statement" and text(n).startswith("continue"):
        return True
    if n.type in ("while_statement", "for_statement", "repeat_while_statement"):
        return False
    return any(_has_continue(c) for c in n.children)


def _has_continue_ir(stmts: list[ir.Stmt]) -> bool:
    return any(isinstance(s, ir.Continue) for s in ir.walk_stmts(stmts))


def _has_error(n: Any) -> bool:
    return bool(n.has_error)


def _first_err(n: Any) -> Any:
    if n.type == "ERROR" or n.is_missing:
        return n
    for c in n.children:
        if c.has_error:
            return _first_err(c)
    return n


def _subst(e: ir.Expr, m: dict[str, ir.Expr]) -> ir.Expr:
    if isinstance(e, ir.Var) and e.name in m:
        return m[e.name]
    changes = {}
    for f in dataclasses.fields(e):
        v = getattr(e, f.name)
        if isinstance(v, ir.Expr):
            changes[f.name] = _subst(v, m)
        elif isinstance(v, tuple) and v and all(isinstance(x, ir.Expr) for x in v):
            changes[f.name] = tuple(_subst(x, m) for x in v)
    return dataclasses.replace(e, **changes) if changes else e


class _Fixed(X):
    """An already-lowered value standing in a normalized expression (the
    target of a compound assignment, read once)."""

    def __init__(self, value: ir.Expr, like: X):
        super().__init__("fixed", like.at, value=value)


class _Shifted:
    """A node parsed from a synthetic source, located at ``anchor``."""

    def __init__(self, node: Any, anchor: Any):
        self._n = node
        self._a = anchor

    def __getattr__(self, name: str) -> Any:
        v = getattr(self._n, name)
        if name in ("children", "named_children"):
            return [_Shifted(c, self._a) for c in v]
        if name in ("start_point", "end_point"):
            return self._a.start_point if name == "start_point" else self._a.end_point
        if name == "parent":
            return _Shifted(v, self._a) if v is not None else None
        return v

    def child_by_field_name(self, f: str) -> Any:
        c = self._n.child_by_field_name(f)
        return _Shifted(c, self._a) if c is not None else None

    def children_by_field_name(self, f: str) -> Any:
        return [_Shifted(c, self._a) for c in self._n.children_by_field_name(f)]

    def field_name_for_child(self, i: int) -> Any:
        return self._n.field_name_for_child(i)

    @property
    def text(self) -> bytes:
        return self._n.text


from .swift_expr import ExprLowerer  # noqa: E402
