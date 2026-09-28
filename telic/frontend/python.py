"""Python -> telic IR.

Supported: top-level functions over ``int``, ``float``, ``bool``, ``str``,
``list[T]`` and frozen dataclass records; ``if``/``while``/``for`` over
``range``/lists/``enumerate``; ``break``/``continue``; ``assert``; ``raise``;
calls to other functions in the program; the numeric builtins. Everything
else is reported as unsupported with a reason and a line -- telic never
guesses at semantics it does not model.
"""

from __future__ import annotations

import ast
import io
import tokenize
from fractions import Fraction

from .. import ir
from ..contracts import (
    FUNCTION_KEYWORDS,
    LOOP_KEYWORDS,
    STATEMENT_KEYWORDS,
    ContractLine,
    ContractSyntaxError,
    parse_comment_lines,
    parse_intent_directive,
)

PY_ASSUMPTIONS = [
    "float is modelled as exact rational arithmetic (rounding error ignored)",
    "distinct list arguments do not alias each other",
    "print() and logging calls have no effect on program state",
]

IGNORED_CALLS = {"print"}
IGNORED_ATTR_CALLS = {"debug", "info", "warning", "error", "exception", "critical"}


class LowerError(Exception):
    def __init__(self, msg: str, node: ast.AST | None = None, line: int | None = None):
        super().__init__(msg)
        self.line = line if line is not None else getattr(node, "lineno", 0)


def _loc(node: ast.AST, line_offset: int = 0, col_offset: int = 0) -> ir.Loc:
    line = getattr(node, "lineno", 0)
    col = getattr(node, "col_offset", 0)
    end_col = getattr(node, "end_col_offset", col) or col
    end_line = getattr(node, "end_lineno", line)
    if line_offset:
        if line == 1:
            col += col_offset
        if end_line == 1:
            end_col += col_offset
        line += line_offset - 1
        end_line += line_offset - 1
    if end_line != line:
        end_col = 0
    return ir.Loc(line, col, end_col)


# ---------------------------------------------------------------------------


class PythonFrontend:
    def __init__(self, path: str, source: str):
        self.path = path
        self.source = source
        self.lines = source.splitlines()
        self.module = ir.Module(path=path, language="python", source=source)
        self.module.assumptions = list(PY_ASSUMPTIONS)
        self.contract_lines: list[ContractLine] = []
        self.signatures: dict[str, tuple[list[ir.Param], ir.Type]] = {}

    # -- entry --------------------------------------------------------------

    def run(self) -> ir.Module:
        try:
            tree = ast.parse(self.source, filename=self.path)
        except SyntaxError as e:
            self.module.problems.append((f"syntax error: {e.msg}", ir.Loc(e.lineno or 0)))
            return self.module
        try:
            self.contract_lines = parse_comment_lines(self._comments(), "#")
        except ContractSyntaxError as e:
            self.module.problems.append((str(e), ir.Loc(e.line, e.col)))
            return self.module

        # Records first, then signatures, then bodies: calls may be forward.
        for node in tree.body:
            if isinstance(node, ast.ClassDef):
                self._record(node)
        for node in tree.body:
            if isinstance(node, ast.FunctionDef):
                try:
                    self.signatures[node.name] = self._signature(node)
                except LowerError as e:
                    self.module.problems.append((f"{node.name}: {e}", ir.Loc(e.line)))
        for node in tree.body:
            if isinstance(node, ast.FunctionDef) and node.name in self.signatures:
                fn = FunctionLowerer(self, node).lower()
                self.module.functions[fn.name] = fn

        # Module-level intent declarations (anything not consumed by a function).
        for cl in self.contract_lines:
            if cl.consumed:
                continue
            if cl.keyword == "intent":
                try:
                    ids, text = parse_intent_directive(cl)
                except ContractSyntaxError as e:
                    self.module.problems.append((str(e), ir.Loc(e.line, e.col)))
                    cl.consumed = True
                    continue
                if text is None:
                    self.module.problems.append(
                        ("'@intent ID' outside a function links nothing; declare with '@intent ID: sentence'", ir.Loc(cl.line, cl.col))
                    )
                else:
                    self.module.intents.append(ir.IntentDecl(ids[0], text, ir.Loc(cl.line, cl.col)))
                cl.consumed = True
        for cl in self.contract_lines:
            if not cl.consumed:
                self.module.problems.append(
                    (f"stray '@{cl.keyword}' is not attached to any function, loop, or statement", ir.Loc(cl.line, cl.col))
                )
        return self.module

    def _comments(self) -> list[tuple[int, int, str]]:
        out = []
        toks = tokenize.generate_tokens(io.StringIO(self.source).readline)
        try:
            for tok in toks:
                if tok.type == tokenize.COMMENT:
                    out.append((tok.start[0], tok.start[1], tok.string))
        except tokenize.TokenError:
            pass
        return out

    # -- declarations -------------------------------------------------------

    def _record(self, node: ast.ClassDef) -> None:
        is_dc = any(
            (isinstance(d, ast.Name) and d.id == "dataclass")
            or (isinstance(d, ast.Call) and isinstance(d.func, ast.Name) and d.func.id == "dataclass")
            or (isinstance(d, ast.Attribute) and d.attr == "dataclass")
            or (isinstance(d, ast.Call) and isinstance(d.func, ast.Attribute) and d.func.attr == "dataclass")
            for d in node.decorator_list
        )
        is_nt = any(isinstance(b, ast.Name) and b.id == "NamedTuple" for b in node.bases)
        if not (is_dc or is_nt):
            return
        fields: list[tuple[str, ir.Type]] = []
        for stmt in node.body:
            if isinstance(stmt, ast.AnnAssign) and isinstance(stmt.target, ast.Name):
                try:
                    t = self.type_of_annotation(stmt.annotation)
                except LowerError:
                    return
                if isinstance(t, ir.TList):
                    return  # records hold scalars / records only
                fields.append((stmt.target.id, t))
        self.module.records[node.name] = ir.TRecord(node.name, tuple(fields))

    def type_of_annotation(self, ann: ast.expr | None) -> ir.Type:
        if ann is None:
            raise LowerError("missing type annotation")
        if isinstance(ann, ast.Constant) and ann.value is None:
            return ir.NONE
        if isinstance(ann, ast.Constant) and isinstance(ann.value, str):
            return self.type_of_annotation(ast.parse(ann.value, mode="eval").body)
        if isinstance(ann, ast.Name):
            simple = {"int": ir.INT, "float": ir.REAL, "bool": ir.BOOL, "str": ir.STR}
            if ann.id in simple:
                return simple[ann.id]
            if ann.id in self.module.records:
                return self.module.records[ann.id]
            raise LowerError(f"unsupported type '{ann.id}'", ann)
        if isinstance(ann, ast.Subscript):
            base = ann.value
            name = base.id if isinstance(base, ast.Name) else base.attr if isinstance(base, ast.Attribute) else None
            if name in {"list", "List", "Sequence"}:
                return ir.TList(self.type_of_annotation(ann.slice))
        raise LowerError(f"unsupported type annotation '{ast.unparse(ann)}'", ann)

    def _signature(self, node: ast.FunctionDef) -> tuple[list[ir.Param], ir.Type]:
        a = node.args
        if a.vararg or a.kwarg or a.kwonlyargs or a.posonlyargs or a.defaults:
            raise LowerError("only plain positional parameters without defaults are supported", node)
        params = []
        for arg in a.args:
            if arg.annotation is None:
                raise LowerError(f"parameter '{arg.arg}' needs a type annotation", arg)
            params.append(ir.Param(arg.arg, self.type_of_annotation(arg.annotation)))
        ret = self.type_of_annotation(node.returns) if node.returns is not None else ir.NONE
        return params, ret


# ---------------------------------------------------------------------------


class FunctionLowerer:
    def __init__(self, fe: PythonFrontend, node: ast.FunctionDef):
        self.fe = fe
        self.node = node
        self.env: dict[str, ir.Type] = {}
        self.fn: ir.Function
        self.tmp = 0
        # contract lines inside this function's line span, not yet consumed
        self.local_contracts = [
            cl for cl in fe.contract_lines if node.lineno <= cl.line <= (node.end_lineno or node.lineno)
        ]
        self.current_intents: list[str] = []

    # -- contract comment association ------------------------------------

    def _header_contracts(self) -> list[ContractLine]:
        node = self.node
        first_line = min([node.lineno] + [d.lineno for d in node.decorator_list])
        above: list[ContractLine] = []
        # Walk upward over contiguous comment lines.
        ln = first_line - 1
        by_line = {l: cl for cl in self.fe.contract_lines for l in cl.raw_lines}
        while ln >= 1:
            text = self.fe.lines[ln - 1].strip()
            if not text.startswith("#"):
                break
            cl = by_line.get(ln)
            if cl is not None and cl.keyword in FUNCTION_KEYWORDS and not cl.consumed:
                if cl not in above:
                    above.append(cl)
            ln -= 1
        above.reverse()
        # Lines between the header and the first real body statement.
        body = node.body
        first = body[0]
        if isinstance(first, ast.Expr) and isinstance(first.value, ast.Constant) and isinstance(first.value.value, str):
            limit = body[1].lineno if len(body) > 1 else (node.end_lineno or node.lineno) + 1
        else:
            limit = first.lineno
        inside = [
            cl
            for cl in self.fe.contract_lines
            if node.lineno < cl.line < limit and cl.keyword in FUNCTION_KEYWORDS and not cl.consumed
        ]
        return above + inside

    def lower(self) -> ir.Function:
        node = self.node
        params, ret = self.fe.signatures[node.name]
        seg = ast.get_source_segment(self.fe.source, node) or ""
        self.fn = ir.Function(
            name=node.name,
            loc=ir.Loc(node.lineno, node.col_offset),
            end_line=node.end_lineno or node.lineno,
            params=params,
            ret=ret,
            source=seg,
            exported=not node.name.startswith("_"),
        )
        for p in params:
            self.env[p.name] = p.ty

        for cl in self._header_contracts():
            cl.consumed = True
            try:
                self._function_contract(cl)
            except (LowerError, ContractSyntaxError) as e:
                self.fn.unsupported.append((f"contract: {e}", ir.Loc(getattr(e, "line", cl.line))))

        body = node.body
        if body and isinstance(body[0], ast.Expr) and isinstance(body[0].value, ast.Constant) and isinstance(body[0].value.value, str):
            body = body[1:]
        self.fn.body = list(self.block(body, node))
        self.fn.locals = dict(self.env)
        return self.fn

    def _function_contract(self, cl: ContractLine) -> None:
        kw = cl.keyword
        if kw == "intent":
            ids, text = parse_intent_directive(cl)
            if text is not None:
                self.fe.module.intents.append(ir.IntentDecl(ids[0], text, ir.Loc(cl.line, cl.col)))
            for i in ids:
                if i not in self.fn.intents:
                    self.fn.intents.append(i)
            self.current_intents = ids
            return
        if kw == "mirrors":
            self.fn.mirrors.append((cl.payload.strip(), ir.Loc(cl.line, cl.col)))
            return
        if kw == "trusted":
            self.fn.trusted = True
            return
        if kw == "pure":
            return
        tags = tuple(cl.tags) or tuple(self.current_intents)
        for t in tags:
            if t not in self.fn.intents:
                self.fn.intents.append(t)
        if kw == "requires":
            self.fn.requires.append(self.clause(cl, "requires", tags))
        elif kw == "ensures":
            self.fn.ensures.append(self.clause(cl, "ensures", tags, result_ty=self.fn.ret))
        elif kw == "decreases":
            self.fn.decreases = self.clause(cl, "decreases", tags, expect=ir.INT)
        elif kw == "raises":
            self.fn.raises.append(self.clause(cl, "raises", tags))

    def clause(
        self,
        cl: ContractLine,
        kind: str,
        tags: tuple[str, ...] = (),
        result_ty: ir.Type | None = None,
        expect: ir.Type = ir.BOOL,
    ) -> ir.Clause:
        text = cl.payload
        if not text:
            raise LowerError(f"empty '@{kind}'", line=cl.line)
        try:
            tree = ast.parse("(" + text + "\n)", mode="eval")
        except SyntaxError as e:
            raise LowerError(f"cannot parse '@{kind}' as a Python expression: {e.msg}", line=cl.line)
        el = ExprLowerer(self, spec=True, result_ty=result_ty, line_offset=cl.line, col_offset=cl.payload_col - 1)
        e = el.expr(tree.body)
        if expect == ir.BOOL:
            e = el.truthy(e, tree.body)
        elif not isinstance(e.ty, ir.TInt):
            raise LowerError(f"'@{kind}' must be an int expression", line=cl.line)
        loc = ir.Loc(cl.line, cl.payload_col, cl.payload_col + len(text) if "\n" not in text else 0)
        return ir.Clause(kind, e, loc, " ".join(text.split()), tags)

    # -- statements ------------------------------------------------------

    def _block_end(self, stmts: list[ast.stmt]) -> int:
        """Last line (inclusive) that belongs to this block, including trailing comments."""
        last = stmts[-1].end_lineno or stmts[-1].lineno
        col = stmts[0].col_offset
        ln = last + 1
        end = last
        while ln <= len(self.fe.lines):
            raw = self.fe.lines[ln - 1]
            s = raw.strip()
            if s == "":
                ln += 1
                continue
            indent = len(raw) - len(raw.lstrip())
            if s.startswith("#") and indent >= col:
                end = ln
                ln += 1
                continue
            break
        return end

    def _stmt_contracts(self, lo: int, hi: int, col: int) -> list[ContractLine]:
        return [
            cl
            for cl in self.local_contracts
            if not cl.consumed and lo < cl.line <= hi and cl.col == col and cl.keyword in STATEMENT_KEYWORDS
        ]

    def block(self, stmts: list[ast.stmt], parent: ast.AST):
        if not stmts:
            return
        col = stmts[0].col_offset
        prev_end = getattr(parent, "lineno", 0)
        for s in stmts:
            for cl in self._stmt_contracts(prev_end, s.lineno - 1, col):
                yield from self._stmt_contract(cl)
            yield from self.stmt(s)
            prev_end = s.end_lineno or s.lineno
        for cl in self._stmt_contracts(prev_end, self._block_end(stmts), col):
            yield from self._stmt_contract(cl)

    def _stmt_contract(self, cl: ContractLine):
        cl.consumed = True
        try:
            c = self.clause(cl, cl.keyword, tuple(cl.tags))
        except LowerError as e:
            self.fn.unsupported.append((str(e), ir.Loc(e.line)))
            yield ir.Unsupported(ir.Loc(cl.line), str(e))
            return
        if cl.keyword == "assert":
            yield ir.AssertStmt(c.loc, c)
        else:
            yield ir.AssumeStmt(c.loc, c)

    def stmt(self, s: ast.stmt):
        try:
            yield from self._stmt(s)
        except LowerError as e:
            self.fn.unsupported.append((str(e), ir.Loc(e.line or s.lineno)))
            yield ir.Unsupported(ir.Loc(s.lineno), str(e))

    def expr(self, e: ast.expr, expect: ir.Type | None = None) -> ir.Expr:
        return ExprLowerer(self).expr(e, expect)

    def cond(self, e: ast.expr) -> ir.Expr:
        el = ExprLowerer(self)
        return el.truthy(el.expr(e), e)

    def declare(self, name: str, ty: ir.Type, node: ast.AST) -> None:
        old = self.env.get(name)
        if old is None:
            self.env[name] = ty
        elif old != ty:
            if isinstance(old, ir.TReal) and isinstance(ty, ir.TInt):
                return  # int value stored in a float variable: promoted on assignment
            if isinstance(old, ir.TList) and isinstance(ty, ir.TList) and ty.elem == ir.NONE:
                return
            raise LowerError(f"variable '{name}' changes type from {old} to {ty}; telic requires one type per variable", node)

    def coerce(self, e: ir.Expr, ty: ir.Type) -> ir.Expr:
        if isinstance(ty, ir.TReal) and isinstance(e.ty, ir.TInt):
            return ir.Builtin(ir.REAL, e.loc, "to_real", (e,))
        if isinstance(ty, ir.TList) and isinstance(e, ir.ListLit) and not e.elems:
            return ir.ListLit(ty, e.loc, ())
        return e

    def fresh(self, base: str) -> str:
        self.tmp += 1
        return f"{base}${self.tmp}"

    def _loop_contracts(self, s: ast.stmt) -> list[ContractLine]:
        """Invariants directly above the loop header or first in its body."""
        out: list[ContractLine] = []
        by_line = {l: cl for cl in self.local_contracts for l in cl.raw_lines}
        ln = s.lineno - 1
        while ln >= 1:
            text = self.fe.lines[ln - 1].strip()
            if not text.startswith("#"):
                break
            cl = by_line.get(ln)
            if cl is not None and cl.keyword in LOOP_KEYWORDS and not cl.consumed and cl not in out:
                out.append(cl)
            ln -= 1
        out.reverse()
        body_first = s.body[0].lineno
        for cl in self.local_contracts:
            if s.lineno < cl.line < body_first and cl.keyword in LOOP_KEYWORDS and not cl.consumed and cl not in out:
                out.append(cl)
        for cl in out:
            cl.consumed = True
        return out

    def _stmt(self, s: ast.stmt):
        loc = ir.Loc(s.lineno, s.col_offset)
        if isinstance(s, ast.Pass):
            return
        if isinstance(s, ast.Expr):
            v = s.value
            if isinstance(v, ast.Constant) and isinstance(v.value, str):
                return  # docstring / bare string
            if isinstance(v, ast.Call):
                f = v.func
                if isinstance(f, ast.Name) and f.id in IGNORED_CALLS:
                    return
                if isinstance(f, ast.Attribute) and f.attr in IGNORED_ATTR_CALLS and isinstance(f.value, ast.Name) and f.value.id in {"logger", "logging", "log"}:
                    return
                if isinstance(f, ast.Attribute) and f.attr == "append" and isinstance(f.value, ast.Name):
                    name = f.value.id
                    t = self.env.get(name)
                    if not isinstance(t, ir.TList):
                        raise LowerError(f"'{name}.append' needs '{name}' to be a list", s)
                    if len(v.args) != 1:
                        raise LowerError("append takes one argument", s)
                    val = self.expr(v.args[0])
                    if t.elem == ir.NONE:
                        t = ir.TList(val.ty)
                        self.env[name] = t
                    yield ir.Append(loc, name, self.coerce(val, t.elem))
                    return
                yield ir.ExprStmt(loc, self.expr(v))
                return
            raise LowerError("expression statement has no effect", s)
        if isinstance(s, ast.AnnAssign):
            if not isinstance(s.target, ast.Name):
                raise LowerError("annotated assignment target must be a name", s)
            ty = self.fe.type_of_annotation(s.annotation)
            self.declare(s.target.id, ty, s)
            if s.value is None:
                return
            val = self.coerce(self.expr(s.value, ty), ty)
            self._check_assignable(s.target.id, ty, val, s)
            yield ir.Assign(loc, s.target.id, val)
            return
        if isinstance(s, ast.Assign):
            if len(s.targets) != 1:
                raise LowerError("chained assignment is not supported", s)
            yield from self._assign(s.targets[0], s.value, s, loc)
            return
        if isinstance(s, ast.AugAssign):
            opnode = ast.BinOp(left=_as_load(s.target), op=s.op, right=s.value)
            ast.copy_location(opnode, s)
            opnode.end_lineno, opnode.end_col_offset = s.end_lineno, s.end_col_offset
            yield from self._assign(s.target, opnode, s, loc)
            return
        if isinstance(s, ast.If):
            c = self.cond(s.test)
            then = tuple(self.block(s.body, s))
            orelse = tuple(self.block(s.orelse, s.orelse[0])) if s.orelse else ()
            yield ir.If(loc, c, then, orelse)
            return
        if isinstance(s, ast.While):
            if s.orelse:
                raise LowerError("while/else is not supported", s)
            contracts = self._loop_contracts(s)
            c = self.cond(s.test)
            body = tuple(self.block(s.body, s))
            for cl in contracts:
                if cl.keyword == "index":
                    raise LowerError("'@index' only applies to for-each loops", line=cl.line)
            invs, dec = self._lower_loop_clauses(contracts)
            yield ir.While(loc, c, invs, dec, body)
            return
        if isinstance(s, ast.For):
            yield from self._for(s, loc)
            return
        if isinstance(s, ast.Return):
            if s.value is None:
                yield ir.Return(loc, None)
            else:
                val = self.coerce(self.expr(s.value, self.fn.ret), self.fn.ret)
                if self.fn.ret == ir.NONE:
                    raise LowerError("function returns a value but is annotated '-> None' (or has no return annotation)", s)
                if val.ty != self.fn.ret:
                    raise LowerError(f"returns {val.ty} but is annotated to return {self.fn.ret}", s)
                yield ir.Return(loc, val)
            return
        if isinstance(s, ast.Break):
            yield ir.Break(loc)
            return
        if isinstance(s, ast.Continue):
            yield ir.Continue(loc)
            return
        if isinstance(s, ast.Assert):
            c = self.cond(s.test)
            text = ast.get_source_segment(self.fe.source, s.test) or ast.unparse(s.test)
            clause = ir.Clause("assert", c, _loc(s.test), " ".join(text.split()))
            yield ir.AssertStmt(loc, clause, native=True)
            return
        if isinstance(s, ast.Raise):
            what = ast.unparse(s.exc) if s.exc is not None else "exception"
            yield ir.Raise(loc, what)
            return
        raise LowerError(f"unsupported statement: {type(s).__name__}", s)

    def _check_assignable(self, name: str, ty: ir.Type, val: ir.Expr, node: ast.AST) -> None:
        if val.ty != ty and not (isinstance(ty, ir.TList) and isinstance(val.ty, ir.TList) and val.ty.elem == ir.NONE):
            raise LowerError(f"cannot assign {val.ty} to '{name}' of type {ty}", node)

    def _assign(self, target: ast.expr, value: ast.expr, s: ast.stmt, loc: ir.Loc):
        if isinstance(target, ast.Name):
            name = target.id
            if name in self.env and isinstance(self.env[name], ir.TList) and any(
                p.name == name for p in self.fn.params
            ):
                raise LowerError(f"rebinding list parameter '{name}' is not supported (mutate it or copy it to a new name)", s)
            known = self.env.get(name)
            val = self.expr(value, known)
            if known is not None:
                val = self.coerce(val, known)
            if isinstance(val.ty, ir.TList) and isinstance(value, ast.Name):
                raise LowerError(
                    f"'{name} = {value.id}' would alias a list; telic models lists as values, so copy explicitly with '{value.id}[:]'",
                    s,
                )
            self.declare(name, val.ty, s)
            ty = self.env[name]
            val = self.coerce(val, ty)
            self._check_assignable(name, ty, val, s)
            yield ir.Assign(loc, name, val)
            return
        if isinstance(target, ast.Subscript) and isinstance(target.value, ast.Name) and not isinstance(target.slice, ast.Slice):
            name = target.value.id
            t = self.env.get(name)
            if not isinstance(t, ir.TList):
                raise LowerError(f"'{name}[...] = ...' needs '{name}' to be a list", s)
            idx = self.expr(target.slice)
            if not isinstance(idx.ty, ir.TInt):
                raise LowerError("list index must be an int", s)
            val = self.coerce(self.expr(value, t.elem), t.elem)
            if val.ty != t.elem:
                raise LowerError(f"cannot store {val.ty} into {t}", s)
            yield ir.IndexAssign(loc, name, idx, val, wrap=True)
            return
        if isinstance(target, ast.Tuple) and isinstance(value, ast.Tuple) and len(target.elts) == len(value.elts):
            # a, b = e1, e2  ==>  t1 = e1; t2 = e2; a = t1; b = t2
            temps = []
            for v in value.elts:
                val = self.expr(v)
                t = self.fresh("tuple")
                self.env[t] = val.ty
                temps.append(t)
                yield ir.Assign(loc, t, val)
            for tgt, t in zip(target.elts, temps):
                load = ast.Name(id=t, ctx=ast.Load())
                ast.copy_location(load, s)
                yield from self._assign(tgt, load, s, loc) if not isinstance(tgt, ast.Name) else self._assign_tmp(tgt.id, t, s, loc)
            return
        raise LowerError(f"unsupported assignment target: {ast.unparse(target)}", s)

    def _assign_tmp(self, name: str, tmp: str, s: ast.stmt, loc: ir.Loc):
        ty = self.env[tmp]
        self.declare(name, ty, s)
        yield ir.Assign(loc, name, self.coerce(ir.Var(ty, loc, tmp), self.env[name]))

    def _lower_loop_clauses(self, contracts: list[ContractLine]):
        invs: list[ir.Clause] = []
        dec = None
        for cl in contracts:
            if cl.keyword == "invariant":
                invs.append(self.clause(cl, "invariant", tuple(cl.tags)))
            elif cl.keyword == "decreases":
                dec = self.clause(cl, "decreases", tuple(cl.tags), expect=ir.INT)
        return tuple(invs), dec

    def _for(self, s: ast.For, loc: ir.Loc):
        if s.orelse:
            raise LowerError("for/else is not supported", s)
        contracts = self._loop_contracts(s)
        index_name = None
        for cl in contracts:
            if cl.keyword == "index":
                index_name = cl.payload.strip()
                if not index_name.isidentifier():
                    raise LowerError("'@index' takes a single name", line=cl.line)
        it = s.iter
        # range(...)
        if isinstance(it, ast.Call) and isinstance(it.func, ast.Name) and it.func.id == "range":
            if not isinstance(s.target, ast.Name):
                raise LowerError("range loop target must be a name", s)
            args = [self.expr(a) for a in it.args]
            if not all(isinstance(a.ty, ir.TInt) for a in args):
                raise LowerError("range() bounds must be ints", s)
            if len(args) == 1:
                lo, hi = ir.Lit(ir.INT, loc, 0), args[0]
            elif len(args) == 2:
                lo, hi = args
            else:
                raise LowerError("range() with a step is not supported", s)
            var = s.target.id
            self.declare(var, ir.INT, s)
            body = tuple(self.block(s.body, s))
            invs, dec = self._lower_loop_clauses(contracts)
            if dec is not None:
                raise LowerError("a for-range loop terminates by construction; remove '@decreases'", line=dec.loc.line)
            yield ir.ForRange(loc, var, lo, hi, invs, body)
            return
        # enumerate(xs) / xs
        idx_visible = False
        if isinstance(it, ast.Call) and isinstance(it.func, ast.Name) and it.func.id == "enumerate":
            if len(it.args) != 1 or not (isinstance(s.target, ast.Tuple) and len(s.target.elts) == 2):
                raise LowerError("use 'for i, x in enumerate(xs)'", s)
            i_node, x_node = s.target.elts
            if not (isinstance(i_node, ast.Name) and isinstance(x_node, ast.Name)):
                raise LowerError("enumerate targets must be names", s)
            idx, elem = i_node.id, x_node.id
            seq_node = it.args[0]
            idx_visible = True
        else:
            if not isinstance(s.target, ast.Name):
                raise LowerError("for-loop target must be a name", s)
            elem = s.target.id
            idx = index_name or self.fresh("i")
            seq_node = it
        seq = self.expr(seq_node)
        if not isinstance(seq.ty, ir.TList):
            raise LowerError("can only iterate over range(...), a list, or enumerate(list)", s)
        self.declare(idx, ir.INT, s)
        self.declare(elem, seq.ty.elem, s)
        body = tuple(self.block(s.body, s))
        if isinstance(seq_node, ast.Name) and seq_node.id in ir.assigned_names(body):
            raise LowerError(f"loop body modifies '{seq_node.id}' while iterating over it", s)
        invs, dec = self._lower_loop_clauses(contracts)
        if dec is not None:
            raise LowerError("a for-each loop terminates by construction; remove '@decreases'", line=dec.loc.line)
        yield ir.ForEach(loc, elem, idx, seq, invs, body, idx_visible=idx_visible or index_name is not None)


def _as_load(target: ast.expr) -> ast.expr:
    node = ast.parse(ast.unparse(target), mode="eval").body
    ast.copy_location(node, target)
    for n in ast.walk(node):
        ast.copy_location(n, target)
        n.end_lineno, n.end_col_offset = target.end_lineno, target.end_col_offset
    return node


# ---------------------------------------------------------------------------


_CMP = {ast.Lt: "lt", ast.LtE: "le", ast.Gt: "gt", ast.GtE: "ge", ast.Eq: "eq", ast.NotEq: "ne"}


class ExprLowerer:
    def __init__(self, fl: FunctionLowerer, spec: bool = False, result_ty: ir.Type | None = None, line_offset: int = 0, col_offset: int = 0):
        self.fl = fl
        self.spec = spec
        self.result_ty = result_ty
        self.line_offset = line_offset
        self.col_offset = col_offset
        self.bound: dict[str, ir.Type] = {}

    def loc(self, node: ast.AST) -> ir.Loc:
        if self.line_offset:
            return _loc(node, self.line_offset, self.col_offset - 1)
        return _loc(node)

    def err(self, msg: str, node: ast.AST) -> LowerError:
        line = self.loc(node).line
        return LowerError(msg, line=line)

    def lookup(self, name: str, node: ast.AST) -> ir.Type:
        if name in self.bound:
            return self.bound[name]
        if name in self.fl.env:
            return self.fl.env[name]
        raise self.err(f"unknown name '{name}'", node)

    def truthy(self, e: ir.Expr, node: ast.AST) -> ir.Expr:
        t = e.ty
        if isinstance(t, ir.TBool):
            return e
        if isinstance(t, ir.TInt):
            return ir.Binary(ir.BOOL, e.loc, "ne", e, ir.Lit(ir.INT, e.loc, 0))
        if isinstance(t, ir.TReal):
            return ir.Binary(ir.BOOL, e.loc, "ne", e, ir.Lit(ir.REAL, e.loc, Fraction(0)))
        if isinstance(t, ir.TList):
            return ir.Binary(ir.BOOL, e.loc, "gt", ir.Builtin(ir.INT, e.loc, "len", (e,)), ir.Lit(ir.INT, e.loc, 0))
        if isinstance(t, ir.TStr):
            return ir.Binary(ir.BOOL, e.loc, "ne", e, ir.Lit(ir.STR, e.loc, ""))
        raise self.err(f"cannot use a {t} as a condition", node)

    def numeric_pair(self, a: ir.Expr, b: ir.Expr, node: ast.AST) -> tuple[ir.Expr, ir.Expr, ir.Type]:
        if not (ir.is_numeric(a.ty) and ir.is_numeric(b.ty)):
            raise self.err(f"arithmetic on {a.ty} and {b.ty}", node)
        if isinstance(a.ty, ir.TReal) or isinstance(b.ty, ir.TReal):
            return self.fl.coerce(a, ir.REAL), self.fl.coerce(b, ir.REAL), ir.REAL
        return a, b, ir.INT

    def expr(self, n: ast.expr, expect: ir.Type | None = None) -> ir.Expr:
        loc = self.loc(n)
        if isinstance(n, ast.Constant):
            v = n.value
            if isinstance(v, bool):
                return ir.Lit(ir.BOOL, loc, v)
            if isinstance(v, int):
                return ir.Lit(ir.INT, loc, v)
            if isinstance(v, float):
                return ir.Lit(ir.REAL, loc, Fraction(repr(v)))
            if isinstance(v, str):
                return ir.Lit(ir.STR, loc, v)
            raise self.err(f"unsupported constant {v!r}", n)
        if isinstance(n, ast.Name):
            if self.spec and n.id == "result" and self.result_ty is not None and n.id not in self.bound:
                if self.result_ty == ir.NONE:
                    raise self.err("'result' used but the function returns nothing", n)
                return ir.Result(self.result_ty, loc)
            return ir.Var(self.lookup(n.id, n), loc, n.id)
        if isinstance(n, ast.UnaryOp):
            a = self.expr(n.operand)
            if isinstance(n.op, ast.Not):
                return ir.Unary(ir.BOOL, loc, "not", self.truthy(a, n.operand))
            if isinstance(n.op, ast.USub):
                if not ir.is_numeric(a.ty):
                    raise self.err(f"cannot negate {a.ty}", n)
                if isinstance(a, ir.Lit) and not isinstance(a.value, bool):
                    return ir.Lit(a.ty, loc, -a.value)  # type: ignore[operator]
                return ir.Unary(a.ty, loc, "neg", a)
            if isinstance(n.op, ast.UAdd):
                return a
            raise self.err("unsupported unary operator", n)
        if isinstance(n, ast.BinOp):
            return self.binop(n, loc)
        if isinstance(n, ast.BoolOp):
            op = "and" if isinstance(n.op, ast.And) else "or"
            vals = [self.truthy(self.expr(v), v) for v in n.values]
            out = vals[0]
            for v in vals[1:]:
                out = ir.Binary(ir.BOOL, loc, op, out, v)
            return out
        if isinstance(n, ast.Compare):
            return self.compare(n, loc)
        if isinstance(n, ast.IfExp):
            c = self.truthy(self.expr(n.test), n.test)
            a = self.expr(n.body, expect)
            b = self.expr(n.orelse, expect)
            if a.ty != b.ty:
                if ir.is_numeric(a.ty) and ir.is_numeric(b.ty):
                    a, b, _ = self.numeric_pair(a, b, n)
                else:
                    raise self.err(f"conditional branches have types {a.ty} and {b.ty}", n)
            return ir.Ite(a.ty, loc, c, a, b)
        if isinstance(n, ast.Call):
            return self.call(n, loc, expect)
        if isinstance(n, ast.Subscript):
            seq = self.expr(n.value)
            if not isinstance(seq.ty, ir.TList):
                raise self.err(f"cannot index a {seq.ty}", n)
            if isinstance(n.slice, ast.Slice):
                if n.slice.step is not None:
                    raise self.err("slices with a step are not supported", n)
                lo = self.expr(n.slice.lower) if n.slice.lower is not None else ir.Lit(ir.NONE, loc, None)
                hi = self.expr(n.slice.upper) if n.slice.upper is not None else ir.Lit(ir.NONE, loc, None)
                for b in (lo, hi):
                    if b.ty not in (ir.INT, ir.NONE):
                        raise self.err("slice bounds must be ints", n)
                return ir.Builtin(seq.ty, loc, "slice", (seq, lo, hi))
            idx = self.expr(n.slice)
            if not isinstance(idx.ty, ir.TInt):
                raise self.err("list index must be an int", n)
            return ir.Index(seq.ty.elem, loc, seq, idx, wrap=True)
        if isinstance(n, ast.Attribute):
            obj = self.expr(n.value)
            if isinstance(obj.ty, ir.TRecord):
                ft = obj.ty.field_type(n.attr)
                if ft is None:
                    raise self.err(f"{obj.ty.name} has no field '{n.attr}'", n)
                return ir.Field(ft, loc, obj, n.attr)
            raise self.err(f"unsupported attribute access '.{n.attr}' on {obj.ty}", n)
        if isinstance(n, ast.List):
            elems = [self.expr(e) for e in n.elts]
            if not elems:
                if isinstance(expect, ir.TList):
                    return ir.ListLit(expect, loc, ())
                return ir.ListLit(ir.TList(ir.NONE), loc, ())
            t = elems[0].ty
            if any(isinstance(e.ty, ir.TReal) for e in elems) and all(ir.is_numeric(e.ty) for e in elems):
                t = ir.REAL
                elems = [self.fl.coerce(e, t) for e in elems]
            if any(e.ty != t for e in elems):
                raise self.err("list elements must all have one type", n)
            return ir.ListLit(ir.TList(t), loc, tuple(elems))
        if isinstance(n, (ast.GeneratorExp, ast.ListComp)):
            raise self.err("comprehensions are only supported inside all(...) / any(...)", n)
        raise self.err(f"unsupported expression: {type(n).__name__}", n)

    def binop(self, n: ast.BinOp, loc: ir.Loc) -> ir.Expr:
        a = self.expr(n.left)
        b = self.expr(n.right)
        op = n.op
        if isinstance(op, ast.Pow):
            if isinstance(n.right, ast.Constant) and isinstance(n.right.value, int) and 0 <= n.right.value <= 4 and ir.is_numeric(a.ty):
                k = n.right.value
                if k == 0:
                    return ir.Lit(a.ty, loc, 1 if isinstance(a.ty, ir.TInt) else Fraction(1))
                out = a
                for _ in range(k - 1):
                    out = ir.Binary(a.ty, loc, "mul", out, a)
                return out
            raise self.err("'**' is supported only with a literal exponent 0..4", n)
        if isinstance(op, ast.Add) and isinstance(a.ty, ir.TList):
            raise self.err("list concatenation is not supported", n)
        if isinstance(op, ast.Add) and isinstance(a.ty, ir.TStr):
            raise self.err("string concatenation is not supported", n)
        if isinstance(op, (ast.Add, ast.Sub, ast.Mult)):
            a, b, t = self.numeric_pair(a, b, n)
            name = {ast.Add: "add", ast.Sub: "sub", ast.Mult: "mul"}[type(op)]
            return ir.Binary(t, loc, name, a, b)
        if isinstance(op, ast.Div):
            a, b, _ = self.numeric_pair(a, b, n)
            return ir.Binary(ir.REAL, loc, "rdiv", self.fl.coerce(a, ir.REAL), self.fl.coerce(b, ir.REAL))
        if isinstance(op, ast.FloorDiv):
            a, b, t = self.numeric_pair(a, b, n)
            if t == ir.INT:
                return ir.Binary(ir.INT, loc, "floordiv", a, b)
            q = ir.Binary(ir.REAL, loc, "rdiv", a, b)
            return ir.Builtin(ir.REAL, loc, "to_real", (ir.Builtin(ir.INT, loc, "floor", (q,)),))
        if isinstance(op, ast.Mod):
            a, b, t = self.numeric_pair(a, b, n)
            if t != ir.INT:
                raise self.err("'%' on floats is not supported", n)
            return ir.Binary(ir.INT, loc, "fmod", a, b)
        raise self.err(f"unsupported operator {type(op).__name__}", n)

    def compare(self, n: ast.Compare, loc: ir.Loc) -> ir.Expr:
        parts = []
        left = self.expr(n.left)
        for op, rnode in zip(n.ops, n.comparators):
            right = self.expr(rnode)
            if isinstance(op, (ast.In, ast.NotIn)):
                if not isinstance(right.ty, ir.TList):
                    raise self.err("'in' needs a list on the right", n)
                lhs = self.fl.coerce(left, right.ty.elem)
                if lhs.ty != right.ty.elem:
                    raise self.err(f"'in' compares {left.ty} against {right.ty}", n)
                c: ir.Expr = ir.Builtin(ir.BOOL, loc, "contains", (right, lhs))
                if isinstance(op, ast.NotIn):
                    c = ir.Unary(ir.BOOL, loc, "not", c)
                parts.append(c)
            elif type(op) in _CMP:
                name = _CMP[type(op)]
                l2, r2 = left, right
                if ir.is_numeric(left.ty) and ir.is_numeric(right.ty):
                    l2, r2, _ = self.numeric_pair(left, right, n)
                elif left.ty != right.ty:
                    raise self.err(f"comparing {left.ty} with {right.ty}", n)
                elif name not in ("eq", "ne") and not ir.is_numeric(left.ty):
                    raise self.err(f"ordering comparison on {left.ty} is not supported", n)
                parts.append(ir.Binary(ir.BOOL, loc, name, l2, r2))
            else:
                raise self.err(f"unsupported comparison {type(op).__name__}", n)
            left = right
        out = parts[0]
        for p in parts[1:]:
            out = ir.Binary(ir.BOOL, loc, "and", out, p)
        return out

    # -- calls ----------------------------------------------------------

    def call(self, n: ast.Call, loc: ir.Loc, expect: ir.Type | None) -> ir.Expr:
        if n.keywords and not (isinstance(n.func, ast.Name) and n.func.id in self.fl.fe.module.records):
            raise self.err("keyword arguments are only supported for record constructors", n)
        f = n.func
        if isinstance(f, ast.Attribute):
            if isinstance(f.value, ast.Name) and f.value.id == "math" and f.attr in ("floor", "ceil", "trunc"):
                (x,) = self._args(n, 1)
                if isinstance(x.ty, ir.TInt):
                    return x
                if not isinstance(x.ty, ir.TReal):
                    raise self.err(f"math.{f.attr} needs a number", n)
                return ir.Builtin(ir.INT, loc, f.attr, (x,))
            if f.attr == "count":
                seq = self.expr(f.value)
                if not isinstance(seq.ty, ir.TList):
                    raise self.err(".count needs a list", n)
                (v,) = self._args(n, 1)
                return ir.Builtin(ir.INT, loc, "count", (seq, self.fl.coerce(v, seq.ty.elem)))
            raise self.err(f"unsupported method call '.{f.attr}(...)'", n)
        if not isinstance(f, ast.Name):
            raise self.err("unsupported call", n)
        name = f.id
        if self.spec and name == "old":
            if self.result_ty is None:
                raise self.err("old(...) is only allowed in '@ensures'", n)
            (x,) = self._args(n, 1)
            return ir.Old(x.ty, loc, x)
        if self.spec and name == "implies":
            a, b = self._args(n, 2)
            return ir.Binary(ir.BOOL, loc, "implies", self.truthy(a, n), self.truthy(b, n))
        if name in ("all", "any"):
            return self.quant(n, loc, "forall" if name == "all" else "exists")
        if name == "len":
            (x,) = self._args(n, 1)
            if not isinstance(x.ty, ir.TList):
                raise self.err("len() is supported on lists", n)
            return ir.Builtin(ir.INT, loc, "len", (x,))
        if name == "abs":
            (x,) = self._args(n, 1)
            if not ir.is_numeric(x.ty):
                raise self.err("abs() needs a number", n)
            return ir.Builtin(x.ty, loc, "abs", (x,))
        if name in ("min", "max"):
            args = [self.expr(a) for a in n.args]
            if len(args) == 1 and isinstance(args[0].ty, ir.TList):
                raise self.err(f"{name}() over a list is not supported; write a loop", n)
            if len(args) < 2 or not all(ir.is_numeric(a.ty) for a in args):
                raise self.err(f"{name}() needs two or more numbers", n)
            t = ir.REAL if any(isinstance(a.ty, ir.TReal) for a in args) else ir.INT
            return ir.Builtin(t, loc, name, tuple(self.fl.coerce(a, t) for a in args))
        if name == "sum":
            (x,) = self._args(n, 1)
            if not (isinstance(x.ty, ir.TList) and ir.is_numeric(x.ty.elem)):
                raise self.err("sum() needs a list of numbers", n)
            return ir.Builtin(x.ty.elem, loc, "sum", (x,))
        if name == "float":
            (x,) = self._args(n, 1)
            if not ir.is_numeric(x.ty):
                raise self.err("float() needs a number", n)
            return self.fl.coerce(x, ir.REAL)
        if name == "int":
            (x,) = self._args(n, 1)
            if isinstance(x.ty, ir.TInt):
                return x
            if isinstance(x.ty, ir.TReal):
                return ir.Builtin(ir.INT, loc, "trunc", (x,))
            raise self.err("int() needs a number", n)
        if name == "round":
            if len(n.args) != 1:
                raise self.err("round() with ndigits is not supported", n)
            (x,) = self._args(n, 1)
            if isinstance(x.ty, ir.TInt):
                return x
            if isinstance(x.ty, ir.TReal):
                return ir.Builtin(ir.INT, loc, "round_even", (x,))
            raise self.err("round() needs a number", n)
        if name == "bool":
            (x,) = self._args(n, 1)
            return self.truthy(x, n)
        if name in self.fl.fe.module.records:
            rec = self.fl.fe.module.records[name]
            vals: dict[str, ir.Expr] = {}
            if len(n.args) > len(rec.fields):
                raise self.err(f"too many arguments to {name}", n)
            for (fname, fty), a in zip(rec.fields, n.args):
                vals[fname] = self.fl.coerce(self.expr(a, fty), fty)
            for kw in n.keywords:
                if kw.arg is None or rec.field_type(kw.arg) is None:
                    raise self.err(f"{name} has no field '{kw.arg}'", n)
                ft = rec.field_type(kw.arg)
                vals[kw.arg] = self.fl.coerce(self.expr(kw.value, ft), ft)  # type: ignore[arg-type]
            missing = [f for f, _ in rec.fields if f not in vals]
            if missing:
                raise self.err(f"{name}(...) is missing {', '.join(missing)}", n)
            for fname, fty in rec.fields:
                if vals[fname].ty != fty:
                    raise self.err(f"field '{fname}' of {name} expects {fty}, got {vals[fname].ty}", n)
            return ir.RecordLit(rec, loc, tuple((f, vals[f]) for f, _ in rec.fields))
        sig = self.fl.fe.signatures.get(name)
        if sig is None:
            raise self.err(f"call to '{name}', which telic cannot see (define it in a checked file with a contract)", n)
        params, ret = sig
        if len(n.args) != len(params):
            raise self.err(f"'{name}' takes {len(params)} arguments, got {len(n.args)}", n)
        args = []
        for p, a in zip(params, n.args):
            v = self.fl.coerce(self.expr(a, p.ty), p.ty)
            if v.ty != p.ty and not (isinstance(p.ty, ir.TList) and isinstance(v.ty, ir.TList) and v.ty.elem == ir.NONE):
                raise self.err(f"argument '{p.name}' of '{name}' expects {p.ty}, got {v.ty}", n)
            args.append(v)
        return ir.Call(ret, loc, name, tuple(args))

    def _args(self, n: ast.Call, k: int) -> list[ir.Expr]:
        if len(n.args) != k:
            raise self.err(f"expected {k} argument(s)", n)
        return [self.expr(a) for a in n.args]

    def quant(self, n: ast.Call, loc: ir.Loc, kind: str) -> ir.Expr:
        if len(n.args) != 1 or not isinstance(n.args[0], (ast.GeneratorExp, ast.ListComp)):
            raise self.err("all()/any() need a generator: all(p(x) for x in xs)", n)
        g = n.args[0]
        if len(g.generators) != 1:
            raise self.err("all()/any() support a single 'for' clause", n)
        gen = g.generators[0]
        it = gen.iter
        saved = dict(self.bound)
        try:
            elem = seq = None
            if isinstance(it, ast.Call) and isinstance(it.func, ast.Name) and it.func.id == "range":
                if not isinstance(gen.target, ast.Name):
                    raise self.err("range generator target must be a name", n)
                bounds = [self.expr(a) for a in it.args]
                if len(bounds) == 1:
                    lo, hi = ir.Lit(ir.INT, loc, 0), bounds[0]
                elif len(bounds) == 2:
                    lo, hi = bounds
                else:
                    raise self.err("range() with a step is not supported", n)
                idx = gen.target.id
                self.bound[idx] = ir.INT
            else:
                if isinstance(it, ast.Call) and isinstance(it.func, ast.Name) and it.func.id == "enumerate":
                    if not (isinstance(gen.target, ast.Tuple) and len(gen.target.elts) == 2 and all(isinstance(t, ast.Name) for t in gen.target.elts)):
                        raise self.err("use 'for i, x in enumerate(xs)'", n)
                    idx = gen.target.elts[0].id  # type: ignore[attr-defined]
                    elem = gen.target.elts[1].id  # type: ignore[attr-defined]
                    seq = self.expr(it.args[0])
                else:
                    if not isinstance(gen.target, ast.Name):
                        raise self.err("generator target must be a name", n)
                    elem = gen.target.id
                    idx = f"{elem}$idx"
                    seq = self.expr(it)
                if not isinstance(seq.ty, ir.TList):
                    raise self.err("generator must range over range(...) or a list", n)
                lo = ir.Lit(ir.INT, loc, 0)
                hi = ir.Builtin(ir.INT, loc, "len", (seq,))
                self.bound[idx] = ir.INT
                self.bound[elem] = seq.ty.elem
            body = self.truthy(self.expr(g.elt), g.elt)
            for cond in gen.ifs:
                c = self.truthy(self.expr(cond), cond)
                body = ir.Binary(ir.BOOL, loc, "implies" if kind == "forall" else "and", c, body)
            return ir.Quant(ir.BOOL, loc, kind, idx, lo, hi, body, elem, seq)
        finally:
            self.bound = saved


def lower_python(path: str, source: str) -> ir.Module:
    return PythonFrontend(path, source).run()
