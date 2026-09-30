"""Calls through function values in Python: which code of the module a call
may run when no ``Call`` in the IR names it (see ``ir.CodeGraph``)."""

from __future__ import annotations

import ast
from typing import Any

from .. import ir

_FUNCS = (ast.FunctionDef, ast.AsyncFunctionDef)
# library functions that neither call nor keep what they are handed
_INERT = {"isinstance", "issubclass", "len", "id", "repr", "str", "type", "callable", "hash", "print", "int", "float", "bool", "format", "hasattr"}
# library functions that never call their positional arguments (a value
# handed to them still escapes)
_READS = {
    "len", "isinstance", "id", "repr", "str", "type", "callable", "hash", "print", "wraps", "update_wrapper", "partial",
    "append", "add", "extend", "insert", "setdefault", "set_defaults", "setattr", "int", "float", "bool", "tuple", "list",
    "dict", "set", "frozenset", "zip", "enumerate", "join", "dumps", "loads", "format", "sorted", "min", "max", "sum",
    "reversed", "range", "Path", "abspath", "relpath", "get", "pop", "update", "discard", "remove", "write", "encode",
}


def code_graph(tree: ast.Module, checked: set[str], indirect: set[str], transparent: set[str], imports: dict[str, tuple[str, str]], modules: set[str], nested: dict[int, str]) -> ir.CodeGraph:
    """``checked``: functions the IR knows, whose direct calls are ``Call``s
    unless they are ``indirect`` (the IR calls a decorator's wrapper, or only
    creates a generator); ``transparent``: decorators that return the
    function itself; ``imports``: names imported from checked modules (and
    ``mod.*`` for ``import mod``), to their module and name there;
    ``modules``: checked modules imported whole; ``nested``: imports inside
    functions (by node id) from checked modules, to their path.

    Targets are names in this module, ``?``, ``@f`` (what the IR's call
    through f's wrapper runs), ``=x`` (the code x is, as a value), or
    ``path::name`` (a name in another module)."""
    g = ir.CodeGraph(imports=dict(imports))
    top = {n.name: n for n in tree.body if isinstance(n, _FUNCS)}
    classes = {n.name: n for n in tree.body if isinstance(n, ast.ClassDef)}
    methods: dict[str, set[str]] = {}  # name -> 'Class.name', properties left out (reading one is not a value)
    defs: dict[str, ast.FunctionDef | ast.AsyncFunctionDef] = dict(top)
    for c in classes.values():
        for st in c.body:
            if isinstance(st, _FUNCS):
                defs[f"{c.name}.{st.name}"] = st
                if not {_name(d) for d in st.decorator_list} & {"property", "cached_property", "setter"}:
                    methods.setdefault(st.name, set()).add(f"{c.name}.{st.name}")
    module_scope: dict[str, Any] = {"parent": None, "params": set(), "data": set(), "opaque": set(), "defs": {}, "assigns": {}, "globals": set(), "cls": None, "self": None}
    for n in tree.body:
        if isinstance(n, (ast.Assign, ast.AnnAssign)) and n.value is not None:
            for t in n.targets if isinstance(n, ast.Assign) else [n.target]:
                if isinstance(t, ast.Name):
                    module_scope["assigns"].setdefault(t.id, []).append(n.value)
                else:
                    module_scope["opaque"].update(x.id for x in ast.walk(t) if isinstance(x, ast.Name))
        elif isinstance(n, (ast.AugAssign, ast.For, ast.AsyncFor, ast.With, ast.AsyncWith)):
            module_scope["opaque"].update(x.id for t in _targets(n) for x in ast.walk(t) if isinstance(x, ast.Name))
    for n in ast.walk(tree):
        if isinstance(n, ast.Global):
            module_scope["opaque"].update(n.names)  # rebound from inside a function: anything
    self_fields: set[str] = set()
    callable_attrs: set[str] = set()

    def project(d: ast.expr) -> bool:
        """Is decorator ``d`` code of this project (its wrapper is, too)?"""
        f = d.func if isinstance(d, ast.Call) else d
        if isinstance(f, ast.Name):
            return f.id in top or f.id in classes or f.id in module_scope["assigns"] or f.id in imports
        return isinstance(f, ast.Attribute) and isinstance(f.value, ast.Name) and f.value.id in modules

    def wrapped(node: ast.FunctionDef | ast.AsyncFunctionDef) -> list[ast.expr]:
        return [d for d in node.decorator_list if _name(d) not in transparent]

    def through(key: str) -> set[str]:
        """What calling ``key`` by name runs."""
        node = defs.get(key)
        if node is not None and any(project(d) for d in wrapped(node)):
            return {"?"}  # the wrapper the decorator returned
        return {key}

    callables = {c.name for c in classes.values() if any(isinstance(st, _FUNCS) and st.name == "__call__" for st in c.body)}

    def may_call(ann: ast.expr | None) -> bool:
        """Can a parameter annotated ``ann`` hold a function?"""
        if ann is None:
            return True
        text = ast.unparse(ann)
        names = {x.id for x in ast.walk(ann) if isinstance(x, ast.Name)} | {x.attr for x in ast.walk(ann) if isinstance(x, ast.Attribute)}
        return bool(names & ({"Callable", "Any", "object", "Protocol", "TypeVar", "Awaitable", "Coroutine"} | callables)) or "Callable" in text or any(len(n) == 1 and n.isupper() for n in names)

    def looked_up(recv: ast.expr, name: ast.expr, scope: dict[str, Any]) -> set[str]:
        """What ``getattr(recv, name)`` may be: methods so named (a constant,
        or an f-string's constant prefix) of a class ``recv`` can be, or a
        field holding a function."""
        if isinstance(recv, ast.Name) and recv.id in scope.get("types", {}):
            ann = scope["types"][recv.id]
            names = {x.id for x in ast.walk(ann) if isinstance(x, ast.Name)} | {x.attr for x in ast.walk(ann) if isinstance(x, ast.Attribute)}
            here = set(classes) | {_name(b) for c in classes.values() for b in c.bases}
            if not names & (here | {"Any", "object", "type", "Type"}) and not any(len(n) == 1 for n in names):
                return set()  # an object of a class defined elsewhere
        if isinstance(name, ast.Constant):
            match = lambda n: n == name.value  # noqa: E731
        elif isinstance(name, ast.JoinedStr) and name.values and isinstance(name.values[0], ast.Constant):
            match = lambda n: n.startswith(str(name.values[0].value))  # noqa: E731
        elif isinstance(name, ast.BinOp) and isinstance(name.left, ast.Constant):
            match = lambda n: n.startswith(str(name.left.value))  # noqa: E731
        else:
            match = lambda n: True  # noqa: E731
        return {m for n, ms in methods.items() if match(n) for m in ms} | ({"?"} if any(match(a) for a in callable_attrs) else set())

    def is_global(x: str, scope: dict[str, Any]) -> bool:
        """Does ``x`` here name what the module binds (no local shadows it)?"""
        while scope["parent"] is not None:
            if x in scope["globals"]:
                return True
            if x in scope["params"] or x in scope["data"] or x in scope["opaque"] or x in scope["defs"] or x in scope["assigns"] or x in scope.get("imported", {}) or x in scope.get("library", ()):
                return False
            scope = scope["parent"]
        return True

    def lookup(x: str, scope: dict[str, Any], seen: set) -> set[str]:
        while scope is not None:
            if scope["parent"] is not None and x in scope["globals"]:
                scope = module_scope
                continue
            if x in scope.get("library", ()):
                return set()
            if x in scope.get("imported", {}):
                return {scope["imported"][x]}
            if x in scope["data"]:
                return set()  # its type holds no function
            if x in scope["params"]:
                return {f"param:{scope['unit']}:{x}"}  # what its callers pass
            if x in scope["opaque"]:
                return {"?"}
            if x in scope["defs"]:
                return {scope["defs"][x]}
            if x in scope["assigns"]:
                if (id(scope), x) in seen:
                    return set()
                seen.add((id(scope), x))
                return set().union(*(resolve(v, scope, seen) for v in scope["assigns"][x]))
            if scope["parent"] is None:
                if x in top:
                    return through(x)
                if x in classes:
                    return {f"{x}.__init__"}
                if x in imports:
                    return {x}
                return set()
            scope = scope["parent"]
        return set()

    def resolve(e: ast.expr, scope: dict[str, Any], seen: set | None = None) -> set[str]:
        """What calling ``e`` may run: functions, units, '?' (unknown)."""
        seen = set() if seen is None else seen
        if isinstance(e, ast.Name):
            return lookup(e.id, scope, seen)
        if isinstance(e, ast.Lambda):
            return {unit_of(e)}
        if isinstance(e, ast.Attribute):
            v = e.value
            if isinstance(v, ast.Name) and v.id == scope.get("self"):
                own = {m for m in methods.get(e.attr, ()) if m.startswith(scope["cls"] + ".")}
                inherits = scope["cls"] not in classes or bool(classes[scope["cls"]].bases)
                if own:
                    return set().union(*(through(m) for m in own))
                return (methods.get(e.attr, set()) if inherits else set()) | ({"?"} if e.attr in self_fields else set())
            if isinstance(v, ast.Name) and v.id in classes and lookup(v.id, scope, set()) == {f"{v.id}.__init__"}:
                return {f"{v.id}.{e.attr}"} if f"{v.id}.{e.attr}" in methods.get(e.attr, ()) else set()
            if isinstance(v, ast.Name) and v.id in modules:
                return {f"{v.id}.{e.attr}"}
            if e.attr == "__call__":
                return resolve(v, scope, seen)
            return set(methods.get(e.attr, ())) | ({"?"} if e.attr in callable_attrs else set())
        if isinstance(e, ast.IfExp):
            return resolve(e.body, scope, seen) | resolve(e.orelse, scope, seen)
        if isinstance(e, ast.BoolOp):
            return set().union(*(resolve(v, scope, seen) for v in e.values))
        if isinstance(e, (ast.NamedExpr, ast.Starred)):
            return resolve(e.value, scope, seen)
        if isinstance(e, ast.Call) and isinstance(e.func, ast.Name) and e.func.id == "getattr" and len(e.args) >= 2:
            return looked_up(e.args[0], e.args[1], scope)
        if isinstance(e, (ast.Call, ast.Subscript, ast.Await)):
            return {"?"}
        return set()

    units: dict[int, str] = {}

    def unit_of(n: ast.AST) -> str:
        if id(n) not in units:
            name = getattr(n, "name", "lambda")
            uid = f"<{name}:{n.lineno}:{n.col_offset}>"
            units[id(n)] = uid
            label = f"the lambda at line {n.lineno}" if isinstance(n, ast.Lambda) else f"'{name}' at line {n.lineno}"
            g.units[uid] = (ir.Loc(n.lineno, n.col_offset), label, ast.unparse(n))
        return units[id(n)]

    def scope_of(fn: ast.AST, parent: dict[str, Any], cls: str | None, unit: str) -> dict[str, Any]:
        a = fn.args
        params = {x.arg for x in a.posonlyargs + a.args + a.kwonlyargs if may_call(x.annotation)} | {x.arg for x in (a.vararg, a.kwarg) if x}
        data = {x.arg for x in a.posonlyargs + a.args + a.kwonlyargs} - params
        types = {x.arg: x.annotation for x in a.posonlyargs + a.args + a.kwonlyargs if x.annotation is not None}
        first = (a.posonlyargs + a.args)[0].arg if cls and (a.posonlyargs + a.args) and not any(_name(d) == "staticmethod" for d in getattr(fn, "decorator_list", [])) else None
        s: dict[str, Any] = {"parent": parent, "params": params, "opaque": set(), "defs": {}, "assigns": {}, "globals": set(), "cls": cls, "self": first, "unit": unit, "data": data, "types": types}
        body = [fn.body] if isinstance(fn, ast.Lambda) else fn.body
        for n in _own(body):
            if isinstance(n, _FUNCS):
                s["defs"][n.name] = unit_of(n)
            elif isinstance(n, ast.ClassDef):
                s["opaque"].add(n.name)
            elif isinstance(n, (ast.Assign, ast.AnnAssign, ast.NamedExpr)) and n.value is not None:
                for t in n.targets if isinstance(n, ast.Assign) else [n.target]:
                    if isinstance(t, ast.Name):
                        s["assigns"].setdefault(t.id, []).append(n.value)
                    else:
                        s["opaque"].update(x.id for x in ast.walk(t) if isinstance(x, ast.Name) and isinstance(x.ctx, ast.Store))
            elif isinstance(n, (ast.Global, ast.Nonlocal)):
                (s["globals"] if isinstance(n, ast.Global) else s["opaque"]).update(n.names)
            elif isinstance(n, ast.ImportFrom) and id(n) in nested:
                s.setdefault("imported", {}).update({x.asname or x.name: f"{nested[id(n)]}::{x.name}" for x in n.names})
            elif isinstance(n, (ast.Import, ast.ImportFrom)):
                s.setdefault("library", set()).update((x.asname or x.name).split(".")[0] for x in n.names)
            elif isinstance(n, ast.ExceptHandler) and n.name:
                s["opaque"].add(n.name)
            else:
                s["opaque"].update(x.id for t in _targets(n) for x in ast.walk(t) if isinstance(x, ast.Name))
        s["opaque"] -= s["globals"]
        return s

    # attributes that may hold a function: assigned one, or annotated Callable
    for n in ast.walk(tree):
        if isinstance(n, ast.AnnAssign) and isinstance(n.target, ast.Name) and "Callable" in ast.unparse(n.annotation):
            callable_attrs.add(n.target.id)
        if isinstance(n, _FUNCS):
            a = n.args
            for x in a.posonlyargs + a.args + a.kwonlyargs:
                if x.annotation is not None and "Callable" in ast.unparse(x.annotation):
                    callable_attrs.add(x.arg)
        if isinstance(n, (ast.Assign, ast.AnnAssign)) and n.value is not None:
            for t in n.targets if isinstance(n, ast.Assign) else [n.target]:
                if isinstance(t, ast.Attribute):
                    if isinstance(t.value, ast.Name) and t.value.id == "self":
                        self_fields.add(t.attr)
                    if isinstance(n.value, (ast.Lambda, ast.Name, ast.Attribute)) and resolve(n.value, module_scope) - {"?"}:
                        callable_attrs.add(t.attr)
    # a parameter annotated Callable and stored in a field makes the field callable
    for n in ast.walk(tree):
        if isinstance(n, ast.Assign) and isinstance(n.value, ast.Name) and n.value.id in callable_attrs:
            callable_attrs.update(t.attr for t in n.targets if isinstance(t, ast.Attribute))

    def value(e: ast.expr, ctx: dict[str, Any]) -> set[str]:
        """Code ``e`` (a value, not called here) refers to. A name from
        another module is marked, as there it may be data, not code."""
        if isinstance(e, ast.Name) and e.id == "self":
            return set()
        if not isinstance(e, (ast.Name, ast.Lambda, ast.Attribute, ast.IfExp, ast.BoolOp, ast.NamedExpr, ast.Starred)):
            return set()
        got = resolve(e, ctx["scope"]) - {"?"}
        if isinstance(e, ast.Name) and got == {f"{e.id}.__init__"}:
            return set()  # a class, not a function
        return {f"={t}" if t in imports or "::" in t or t.split(".")[0] in modules else t for t in got}

    def site(ctx: dict[str, Any], loc: ast.AST, label: str, targets: set[str]) -> None:
        if targets and ctx["unit"] is not None:
            g.calls.append((ctx["unit"], ir.Loc(loc.lineno, loc.col_offset), label if len(label) <= 40 else label[:37] + "...", tuple(sorted(targets))))

    parents = {id(c): n for n in ast.walk(tree) for c in ast.iter_child_nodes(n)}

    def escapes(n: ast.AST, ctx: dict[str, Any]) -> bool:
        """Does the value ``n`` leave where telic follows it: returned,
        yielded, stored in a field or container, a default, or handed to
        code that is not the project's? (Compared, iterated or tested, it
        does not.)"""
        p = parents.get(id(n))
        while isinstance(p, (ast.IfExp, ast.BoolOp, ast.NamedExpr, ast.Starred, ast.keyword)) and not (isinstance(p, ast.IfExp) and p.test is n):
            n, p = p, parents.get(id(p))
        if isinstance(p, (ast.Return, ast.Yield, ast.YieldFrom, ast.List, ast.Tuple, ast.Set, ast.Dict, ast.ListComp, ast.SetComp, ast.GeneratorExp, ast.DictComp, ast.arguments)):
            return True
        if isinstance(p, ast.Lambda):
            return p.body is n
        if isinstance(p, (ast.Assign, ast.AnnAssign, ast.AugAssign)):
            return p.value is n
        if isinstance(p, ast.Call):
            return n is not p.func and _name(p.func) not in _INERT and not callees_of(p.func, ctx["scope"])[0]
        return False

    def visit(node: ast.AST, ctx: dict[str, Any], quiet: bool = False) -> None:
        """``quiet``: ``node`` is a value tracked by name (``g = f``), so
        referring to code there does not let it escape."""
        if isinstance(node, (*_FUNCS, ast.Lambda)):
            if isinstance(node, _FUNCS):
                decorate(node, ctx, unit_of(node))
            for d in node.args.defaults + [x for x in node.args.kw_defaults if x is not None]:
                visit(d, ctx)
            uid = unit_of(node)
            if isinstance(node, ast.Lambda) and not quiet and escapes(node, ctx):
                g.escaped.add(uid)
            if isinstance(node, _FUNCS) and wrapped(node):
                g.escaped.add(uid)
            inner = {"unit": uid, "checked": False, "scope": scope_of(node, ctx["scope"], None, uid)}
            for st in [node.body] if isinstance(node, ast.Lambda) else node.body:
                visit(st, inner)
            return
        if isinstance(node, ast.ClassDef):
            for d in node.decorator_list + node.bases + [k.value for k in node.keywords]:
                visit(d, ctx)
            for st in node.body:
                if isinstance(st, _FUNCS):
                    decorate(st, ctx, unit_of(st))
                    uid = unit_of(st)
                    inner = {"unit": uid, "checked": False, "scope": scope_of(st, ctx["scope"], node.name, uid)}
                    g.escaped.add(uid)  # a method of a class telic does not check
                    for s in st.body:
                        visit(s, inner)
                else:
                    visit(st, ctx)
            return
        if isinstance(node, ast.Call):
            call(node, ctx)
            return
        if isinstance(node, (ast.Assign, ast.AnnAssign)) and node.value is not None:
            targets = node.targets if isinstance(node, ast.Assign) else [node.target]
            tracked = all(isinstance(t, ast.Name) for t in targets)
            for t in targets:
                visit(t, ctx)
            visit(node.value, ctx, quiet=tracked)
            return
        if isinstance(node, (ast.Name, ast.Attribute, ast.IfExp, ast.BoolOp, ast.NamedExpr, ast.Starred)) and isinstance(getattr(node, "ctx", ast.Load()), ast.Load):
            if not quiet and escapes(node, ctx):
                g.escaped.update(value(node, ctx))
            if isinstance(node, ast.Attribute):
                visit(node.value, ctx, quiet=True)
                return
        for c in ast.iter_child_nodes(node):
            visit(c, ctx, quiet=quiet and isinstance(node, (ast.IfExp, ast.BoolOp)))

    def call(node: ast.Call, ctx: dict[str, Any]) -> None:
        f, scope = node.func, ctx["scope"]
        label = ast.unparse(f)
        if isinstance(f, ast.Name):
            t = resolve(f, scope)
            if ctx["checked"] and f.id in checked and is_global(f.id, scope):
                if f.id in indirect:
                    site(ctx, node, label, {f"@{f.id}"})
            elif not (ctx["checked"] and t == {f"{f.id}.__init__"}):  # a class: 'New' in the IR
                site(ctx, node, label, t)
        elif isinstance(f, ast.Attribute):
            v = f.value
            if isinstance(v, ast.Name) and v.id == scope.get("self"):
                if not (ctx["checked"] and f.attr in methods):
                    site(ctx, node, label, resolve(f, scope))
                elif methods[f.attr] & indirect:
                    site(ctx, node, label, {f"@{m}" for m in methods[f.attr] & indirect})
            elif isinstance(v, ast.Name) and v.id in modules:
                site(ctx, node, label, {f"{v.id}.{f.attr}"} if not ctx["checked"] else set())
            elif f.attr == "__call__" or f.attr in callable_attrs and f.attr not in methods:
                site(ctx, node, label, resolve(v, scope) if f.attr == "__call__" else {"?"})
            elif not ctx["checked"] and f.attr in methods and not (isinstance(v, ast.Name) and v.id in module_scope["assigns"]):
                site(ctx, node, label, set(methods[f.attr]))
            visit(v, ctx, quiet=True)
        else:
            t = resolve(f, scope)
            site(ctx, node, label, t or {"?"})
            if isinstance(f, ast.Lambda):
                visit(f, ctx, quiet=True)
            else:
                visit(f, ctx)
        callees, bound = callees_of(f, scope)
        given: set[str] = set()
        for i, a in enumerate(node.args):
            if isinstance(a, ast.Starred):
                g.flows.append((callees, "*", ("?",)))
            elif callees:
                got = passed(a, scope)
                if got:
                    g.flows.append((callees, f"^{i}" if bound else i, tuple(sorted(got))))
        for k in node.keywords:
            got = passed(k.value, scope)
            if callees and got:
                g.flows.append((callees, k.arg or "*", tuple(sorted(got)) if k.arg else ("?",)))
        reads = _name(f) in _READS  # positional arguments are not called; key= may be
        for a in node.args + [k.value for k in node.keywords]:
            if not (reads and not any(a is k.value and k.arg in ("key", "default_factory") for k in node.keywords)):
                for x in ast.walk(a):
                    if isinstance(x, (ast.Name, ast.Attribute, ast.Lambda)) and _value_position(x, a):
                        # a parameter handed on: only the functions its callers pass
                        given |= {f"={t}" if t.startswith("param:") else t for t in value(x, ctx)}
            visit(a, ctx)
        if given and not callees:
            # code telic does not see may call what it is handed
            site(ctx, node, f"{label} (given {', '.join(sorted(_short(x) for x in given))})", given)

    def decorate(fn: ast.FunctionDef | ast.AsyncFunctionDef, ctx: dict[str, Any], target: str) -> None:
        """``@d def f``: ``d`` is called with ``f``."""
        for d in fn.decorator_list:
            if isinstance(d, (ast.Name, ast.Attribute)):
                callees, _ = callees_of(d, ctx["scope"])
                if callees:
                    g.flows.append((callees, 0, (target,)))
            else:
                visit(d, ctx)

    def passed(a: ast.expr, scope: dict[str, Any]) -> set[str]:
        """What an argument may be, as far as calling it goes."""
        return {f"={t}" if t in imports or "::" in t or t.split(".")[0] in modules else t for t in resolve(a, scope)}

    def callees_of(f: ast.expr, scope: dict[str, Any]) -> tuple[tuple[str, ...], int]:
        """The functions of the project a call may enter by name, and 1 if
        it is a method call whose receiver fills 'self'."""
        if isinstance(f, ast.Name):
            t = resolve(f, scope)
            return tuple(sorted(x for x in t if x != "?" and not x.startswith("param:"))), 0
        if isinstance(f, ast.Attribute):
            v = f.value
            if isinstance(v, ast.Name) and v.id in modules:
                return (f"{v.id}.{f.attr}",), 0
            if isinstance(v, ast.Name) and v.id in classes and is_global(v.id, scope):
                return tuple(sorted(m for m in methods.get(f.attr, ()) if m.startswith(v.id + "."))), 0
            return tuple(sorted(methods.get(f.attr, ()))), 1
        return (), 0

    g.passthrough = {k for k in defs if k in indirect and through(k) == {k}}
    for key, node in defs.items():
        if key not in checked:
            g.units[key] = (ir.Loc(node.lineno, node.col_offset), f"'{key}'", ast.unparse(node))
    for n in tree.body:
        if isinstance(n, _FUNCS):
            decorate(n, {"unit": None, "checked": False, "scope": module_scope}, n.name)
            if wrapped(n):
                g.escaped.add(n.name)
            ctx = {"unit": n.name, "checked": n.name in checked, "scope": scope_of(n, module_scope, None, n.name)}
            for st in n.body:
                visit(st, ctx)
        elif isinstance(n, ast.ClassDef):
            for d in n.decorator_list + n.bases + [k.value for k in n.keywords]:
                visit(d, {"unit": None, "checked": False, "scope": module_scope})
            for st in n.body:
                if isinstance(st, _FUNCS):
                    key = f"{n.name}.{st.name}" + (".setter" if any(_name(d) == "setter" for d in st.decorator_list) else "")
                    decorate(st, {"unit": None, "checked": False, "scope": module_scope}, key)
                    if wrapped(st):
                        g.escaped.add(key)
                    ctx = {"unit": key, "checked": key in checked, "scope": scope_of(st, module_scope, n.name, key)}
                    for s in st.body:
                        visit(s, ctx)
                else:
                    visit(st, {"unit": None, "checked": False, "scope": module_scope})
        else:
            tracked = isinstance(n, (ast.Assign, ast.AnnAssign)) and all(isinstance(t, ast.Name) for t in (n.targets if isinstance(n, ast.Assign) else [n.target]))
            visit(n, {"unit": None, "checked": False, "scope": module_scope}, quiet=tracked)
    for x in module_scope["assigns"]:
        got = lookup(x, module_scope, set())
        if got:
            g.bindings[x] = tuple(sorted(got))
    return g


def _value_position(x: ast.AST, root: ast.AST) -> bool:
    """Is ``x`` (inside ``root``) used as a value, not called and not the
    receiver of an attribute?"""
    for p in ast.walk(root):
        if isinstance(p, ast.Call) and p.func is x:
            return False
        if isinstance(p, ast.Attribute) and p.value is x:
            return False
        if isinstance(p, ast.Lambda) and x is not p and any(x is y for y in ast.walk(p.body)):
            return False
    return True


def _short(t: str) -> str:
    return t.strip("<>").split(":")[0] if t.startswith("<") else t


def _name(d: ast.expr) -> str:
    if isinstance(d, ast.Call):
        d = d.func
    if isinstance(d, ast.Attribute):
        return d.attr
    return d.id if isinstance(d, ast.Name) else "?"


def _targets(n: ast.AST) -> list[ast.expr]:
    if isinstance(n, (ast.For, ast.AsyncFor, ast.comprehension, ast.AugAssign)):
        return [n.target]
    if isinstance(n, (ast.With, ast.AsyncWith)):
        return [i.optional_vars for i in n.items if i.optional_vars is not None]
    return []


def _own(body: list[ast.AST]):
    """Nodes of a body, not descending into nested functions, lambdas or classes."""
    stack = list(body)
    while stack:
        n = stack.pop()
        yield n
        if not isinstance(n, (*_FUNCS, ast.ClassDef, ast.Lambda)):
            stack.extend(ast.iter_child_nodes(n))
