"""Whole-program facts the verifier needs: name resolution, the call graph,
recursion SCCs, which functions are *definitional* (usable inside specs), and
which list parameters a function mutates."""

from __future__ import annotations

import dataclasses
import re
from dataclasses import dataclass, field
from typing import Any

from . import ir


_LANGS = {"typescript": "TypeScript", "swift": "Swift", "python": "Python", "rust": "Rust"}

# The node for a call through a function value of unknown origin: it may run
# any function whose value escaped (was stored, returned, passed or decorated).
ANY = "::a function passed as a value"


@dataclass
class FuncRef:
    module: ir.Module
    fn: ir.Function

    @property
    def key(self) -> str:
        return f"{self.module.path}::{self.fn.name}"


@dataclass
class Program:
    modules: list[ir.Module]
    funcs: dict[str, FuncRef] = field(default_factory=dict)
    callees: dict[str, set[str]] = field(default_factory=dict)
    scc_of: dict[str, int] = field(default_factory=dict)
    recursive: set[str] = field(default_factory=set)
    definitional: set[str] = field(default_factory=set)
    # '@trusted' functions returning a scalar with an '@ensures': specs may
    # call them, and each use is unfolded one level through the '@ensures'
    predicates: set[str] = field(default_factory=set)
    # functions whose proofs may unfold a predicate (their own contracts,
    # body, or a callee's contract calls one)
    predicate_users: set[str] = field(default_factory=set)
    mutated: dict[str, set[str]] = field(default_factory=dict)
    appends: dict[str, set[str]] = field(default_factory=dict)
    # per function: variables holding the same object as an unchecked value
    # (a checked view of one, or a checked value handed to unchecked code)
    views: dict[str, set[str]] = field(default_factory=dict)
    # functions that may change an object unchecked values can reach
    unchecked_writers: set[str] = field(default_factory=set)
    # functions that may hand a checked object to unchecked code (or store one
    # where unchecked code may reach it), directly or through calls
    hands_out: set[str] = field(default_factory=set)
    logic_names: dict[str, str] = field(default_factory=dict)
    classes: dict[str, ir.ClassDecl] = field(default_factory=dict)
    class_module: dict[str, ir.Module] = field(default_factory=dict)
    # 'Class.field' -> targets written: a parameter name, '*' (any object),
    # or '@new' (only objects allocated during the call).
    heap_writes: dict[str, dict[str, set[str]]] = field(default_factory=dict)
    heap_reads: dict[str, set[str]] = field(default_factory=dict)
    allocates: set[str] = field(default_factory=set)
    # module path -> class name it uses that telic cannot attribute to one definition -> why
    ambiguous: dict[str, dict[str, str]] = field(default_factory=dict)
    # method key -> keys of every override (a call through the base may run any of them)
    dispatch: dict[str, set[str]] = field(default_factory=dict)
    # override key -> (class, index) of invariants of its own class that a call
    # through a base does not establish, so its entry may not assume them
    untrusted: dict[str, set[tuple[str, int]]] = field(default_factory=dict)
    # code telic does not check as a function (a lambda, a nested function, a
    # method of an unchecked class): key -> (module, loc, label, source)
    units: dict[str, tuple[ir.Module, ir.Loc, str, str]] = field(default_factory=dict)
    # function key -> (loc, callee as written, keys it may run) for each call
    # through a function value, which no 'Call' names
    code_calls: dict[str, list[tuple[ir.Loc, str, set[str]]]] = field(default_factory=dict)
    later: dict[str, set[str]] = field(default_factory=dict)  # scheduled only: effects, not recursion
    passthrough: set[str] = field(default_factory=set)  # see ir.CodeGraph.passthrough

    @classmethod
    def build(cls, modules: list[ir.Module]) -> "Program":
        p = cls(modules)
        qualify_classes(modules)
        p.ambiguous = {m.path: dict(m.ambiguous_classes) for m in modules if m.ambiguous_classes}
        for m in modules:
            for f in m.functions.values():
                if f.trusted:
                    # a trusted body is never checked: only its contract must be understood
                    f.unsupported = [(msg, loc) for msg, loc in f.unsupported if msg.startswith("contract:")]
                ref = FuncRef(m, f)
                p.funcs[ref.key] = ref
        p._unawaited()
        for m in modules:
            for cname, decl in m.classes.items():
                p.classes[cname] = decl
                p.class_module[cname] = m
        p._overrides()
        for m in modules:
            for name in m.code.passthrough:
                ref = p.own(m, name)
                if ref is not None:
                    p.passthrough.add(ref.key)
        p._call_graph()
        p._code_values()
        p._opaque_subclasses()
        p._escaping_constructors()
        p._sccs()
        p._mutation()
        p._unchecked_writes()
        p._hands_out()
        p._heap()
        p._predicates()
        p._definitional()
        p._names()
        return p

    def mro(self, cls: str) -> list[str]:
        out: list[str] = []

        def walk(c: str) -> None:
            if c in out or c not in self.classes:
                return
            out.append(c)
            for b in self.classes[c].bases:
                walk(b)

        walk(cls)
        return out

    def member(self, cls: str, meth: str) -> "FuncRef | None":
        """``cls.meth``, its own or inherited (constructors included)."""
        for c in self.mro(cls):
            ref = self.funcs.get(f"{self.class_module[c].path}::{c}.{meth}")
            if ref is not None:
                return ref
        return None

    def lifecycles_for(self, cls: str, never: bool = False) -> list[tuple[str, ir.Lifecycle]]:
        """(owner, lifecycle) for every lifecycle an object of static type
        ``cls`` keeps: its classes', and its subclasses' (it may be one).
        ``never`` lines are consequences, not constraints: only on request."""
        owners = self.mro(cls) + [c for c in self.classes if c != cls and cls in self.mro(c)]
        return [(c, lc) for c in owners for lc in self.classes[c].lifecycles if never or lc.kind != "never"]

    def in_hierarchy(self, cls: str) -> bool:
        """Does ``cls`` share field maps with other classes (bases or subclasses)?"""
        decl = self.classes.get(cls)
        return bool(decl and decl.bases) or any(cls in d.bases for d in self.classes.values())

    def _overrides(self) -> None:
        """Calls resolve by static type, so a call through a base class may run
        an override: an override without a contract inherits its base's (and
        is checked against it); one with a different contract is reported;
        and every call through the base depends on all overrides."""
        for cname in self.classes:
            m = self.class_module[cname]
            ancestors = self.mro(cname)[1:]
            if not ancestors:
                continue
            for fn in m.functions.values():
                if not fn.name.startswith(cname + "."):
                    continue
                meth = fn.name[len(cname) + 1 :]
                if meth in ("__init__", "__post_init__"):
                    continue
                roots = [a for a in ancestors if f"{self.class_module[a].path}::{a}.{meth}" in self.funcs]
                if roots:
                    self._untrusted(f"{m.path}::{fn.name}", cname, roots)
                for a in ancestors:
                    base = self.funcs.get(f"{self.class_module[a].path}::{a}.{meth}")
                    if base is None:
                        continue
                    self.dispatch.setdefault(base.key, set()).add(f"{m.path}::{fn.name}")
                    bf = base.fn
                    has = lambda f: bool(f.requires or f.ensures or f.raises)  # noqa: E731
                    if has(bf) and not has(fn):
                        if [x.name for x in bf.params] != [x.name for x in fn.params]:
                            fn.unsupported.append((f"overrides {bf.name} with different parameter names, so it cannot inherit its contract; use the same names", fn.loc))
                        else:
                            fn.requires, fn.ensures, fn.raises = list(bf.requires), list(bf.ensures), list(bf.raises)
                    elif has(bf) and [c.text for c in bf.requires + bf.ensures + bf.raises] != [c.text for c in fn.requires + fn.ensures + fn.raises]:
                        fn.unsupported.append((f"overrides {bf.name} with a different contract; calls through {a} are checked against {bf.name}'s, so keep it (or remove this one to inherit it)", fn.loc))
                    break
        # transitively: overrides of overrides
        changed = True
        while changed:
            changed = False
            for k, subs in self.dispatch.items():
                more = set().union(*(self.dispatch.get(x, set()) for x in subs)) - subs
                if more:
                    subs |= more
                    changed = True

    def _unawaited(self) -> None:
        """A call to an async function that is not awaited returns before
        the callee finishes (Python runs none of it yet, JavaScript runs it
        up to its first await): the caller gets neither its effects nor its
        postcondition, so the call is unchecked code that may touch its
        arguments."""
        for ref in self.funcs.values():

            def swap(e: ir.Expr, parent: ir.Expr | None) -> ir.Expr | None:
                if not isinstance(e, ir.Call) or (isinstance(parent, ir.Builtin) and parent.name == "await"):
                    return None
                tgt = self.resolve(ref.module, e.func)
                if tgt is None or not tgt.fn.is_async:
                    return None
                return ir.Extern(e.ty, e.loc, f"{ir.source_name(e.func)} (not awaited)", e.args)

            ref.fn.body = _rewrite_stmts(ref.fn.body, swap)

    def _untrusted(self, key: str, cname: str, roots: list[str]) -> None:
        """A call typed as a base ``r`` establishes ``r``'s invariants only,
        and code typed ``r`` may have changed any field ``r`` has without
        checking a subclass's invariant over it: the override may assume a
        subclass invariant only if it reads no such field."""
        out: set[tuple[str, int]] = set()
        decl = self.classes[cname]
        for c in self.mro(cname):
            for i, inv in enumerate(self.classes[c].invariants):
                read = {x.name for x in ir.walk_expr(inv.expr) if isinstance(x, ir.Field) and isinstance(x.obj, ir.Var) and x.obj.name == "self"}
                for r in roots:
                    seen = set(self.mro(r))
                    if c not in seen and any(decl.field_owner(f) in seen for f in read):
                        out.add((c, i))
        if out:
            self.untrusted[key] = out

    def _escaping_constructors(self) -> None:
        """A constructor that hands ``self`` to other code before a subclass
        has initialised its own fields lets that code run an override on a
        half-built object: its fields unset, its invariants not established."""
        for cname in self.classes:
            subs = [c for c in self.classes if c != cname and cname in self.mro(c)]
            ref = self.funcs.get(f"{self.class_module[cname].path}::{cname}.__init__")
            if not subs or ref is None:
                continue
            for x in _escapes_of_self(ref.fn.body):
                what = f"'{ir.source_name(x.func)}'" if isinstance(x, (ir.Call, ir.Extern)) else "other code"
                ref.fn.unsupported.append((f"the constructor hands 'self' to {what} before {ir.source_name(subs[0])}, a subclass, has set its own fields; an override could run on a half-built object", x.loc))
                break

    def _opaque_subclasses(self) -> None:
        """A checked class with a subclass the frontend does not model: a call
        to its methods may run an override telic never saw, so it is not checked."""
        opened: dict[str, str] = {}
        for m in self.modules:
            for sub, base, loc in m.opaque_subclasses:
                b = base.rsplit(".", 1)[-1]
                for c in self.classes:
                    if ir.source_name(c) == b and (self.class_module[c] is m or self.class_module[c].path == m.class_origin.get(c)):
                        for a in self.mro(c):
                            where = f"{sub} ({m.path}:{loc.line}) extends {b}, which telic does not check" if sub else f"{b} is used as a value at {m.path}:{loc.line}, so it may be subclassed where telic does not look"
                            opened.setdefault(a, f"{where}; a call to a method of {ir.source_name(a)} may run an override it never checked")
                            opened.setdefault(a, f"{sub} ({m.path}:{loc.line}) extends {b}, and telic does not model {_LANGS.get(m.language, m.language)} inheritance, so a call to a method of {ir.source_name(a)} may run an override it never checked")
        if not opened:
            return
        methods = {k: opened[c] for k, r in self.funcs.items() for c in opened if r.fn.name.startswith(c + ".") and not r.fn.name.endswith(".__init__")}
        for k in methods:
            self.dispatch.setdefault(k, set())
        for key, ref in self.funcs.items():
            why = next((methods[c] for c in sorted(self.callees.get(key, ())) if c in methods and c != key), None)
            if why is not None:
                ref.fn.unsupported.append((why, ref.fn.loc))

    def own(self, module: ir.Module, name: str) -> FuncRef | None:
        """A function of ``module`` by the name its source gives it (a class
        of the same name elsewhere qualifies it: ``Lowerer@rust.run``)."""
        hit = self.funcs.get(f"{module.path}::{name}")
        if hit is None:
            hit = next((self.funcs[f"{module.path}::{f}"] for f in sorted(module.functions) if ir.source_name(f) == name), None)
        return hit

    def through_wrapper(self, module: ir.Module, name: str) -> FuncRef | None:
        """The checked function an unchecked call ``@wrapper f`` runs with the
        same arguments (``passthrough``), or None."""
        if not name.startswith("@") or " " not in name:
            return None
        tgt = self.resolve(module, name.split(" ", 1)[1])
        return tgt if tgt is not None and tgt.key in self.passthrough else None

    def resolve(self, module: ir.Module, name: str) -> FuncRef | None:
        hit = self.funcs.get(f"{module.path}::{name}")
        if hit is not None:
            return hit
        if name in module.imports:
            path, remote = module.imports[name]
            return self.funcs.get(f"{path}::{remote}")
        if "." in name:
            cls = name.split(".", 1)[0]
            home = self.class_module.get(cls)
            if home is not None and home is not module:
                return self.funcs.get(f"{home.path}::{name}")
        return None

    def ambiguity(self, ref: FuncRef) -> str | None:
        """Why ``ref`` cannot be checked soundly: it mentions a class name that
        several checked files define and telic cannot tell which one is
        meant (conservatively, by any mention in its IR)."""
        names = self.ambiguous.get(ref.module.path)
        if not names:
            return None
        text = repr(ref.fn)
        for cname, why in names.items():
            if f"'{cname}'" in text or f"'{cname}." in text or ref.fn.name.startswith(cname + "."):
                return why
        return None

    def ref(self, key: str) -> FuncRef:
        #@ requires key in self.funcs
        return self.funcs[key]

    # ------------------------------------------------------------------

    def _calls_in(self, ref: FuncRef) -> set[str]:
        out: set[str] = set()
        exprs: list[ir.Expr] = []
        for s in ir.walk_stmts(ref.fn.body):
            exprs.extend(ir.stmt_exprs(s))
            if isinstance(s, (ir.While, ir.ForRange, ir.ForEach)):
                exprs.extend(c.expr for c in s.invariants)
            if isinstance(s, (ir.AssertStmt, ir.AssumeStmt)):
                exprs.append(s.clause.expr)
        for c in ref.fn.requires + ref.fn.ensures + ref.fn.raises:
            exprs.append(c.expr)
        for e in exprs:
            for sub in ir.walk_expr(e):
                if isinstance(sub, ir.Call):
                    tgt = self.resolve(ref.module, sub.func)
                    if tgt is not None:
                        out.add(tgt.key)
                elif isinstance(sub, ir.Extern):
                    tgt = self.through_wrapper(ref.module, sub.name)
                    if tgt is not None:
                        out.add(tgt.key)
                elif isinstance(sub, ir.New):
                    for m in ("__init__", "__post_init__"):
                        tgt = self.member(sub.cls, m)
                        if tgt is not None:
                            out.add(tgt.key)
        return out

    def _call_graph(self) -> None:
        for key, ref in self.funcs.items():
            self.callees[key] = self._calls_in(ref)

    def _code_values(self) -> None:
        """Edges no ``Call`` shows: calls through function values, lambdas,
        nested functions and decorators' wrappers (``ir.CodeGraph``). ``ANY``
        leads to every function whose value escaped."""
        by_path = {m.path: m for m in self.modules}

        def res(m: ir.Module, name: str, seen: set[tuple[str, str]]) -> set[str]:
            if (m.path, name) in seen:
                return set()
            seen.add((m.path, name))
            if name == "?":
                return {ANY}
            if name.startswith("param:"):
                unit, param = name[len("param:"):].rsplit(":", 1)
                keys = res(m, unit, set())
                key = next(iter(keys)) if len(keys) == 1 else None
                if key is None or key not in self.funcs or key in escaped or key in starred:
                    return {ANY}
                return set().union(*(res(fm, t, seen) for fm, t in into.get((key, param), ())))
            if name.startswith("="):
                return res(m, name[1:], seen) - {ANY}
            if name.startswith("@"):
                tgt = self.own(m, name[1:]) or self.resolve(m, name[1:])
                return set() if tgt is not None and tgt.key in self.passthrough else {ANY}  # else a wrapper runs
            if "::" in name:
                path, rest = name.split("::", 1)
                other = by_path.get(path)
                return res(other, rest, seen) if other is not None else set()
            if name in m.functions:
                return {f"{m.path}::{name}"}
            hit = sorted(f for f in m.functions if ir.source_name(f) == name)
            if hit:
                return {f"{m.path}::{hit[0]}"}
            if name in m.code.units:
                return {f"{m.path}::{name}"}
            if name in m.code.bindings:
                return set().union(*(res(m, t, seen) for t in m.code.bindings[name]))
            where = m.code.imports.get(name) or m.imports.get(name)
            if where is None and "." in name:
                head, rest = name.split(".", 1)
                if f"{head}.*" in m.code.imports:
                    where = (m.code.imports[f"{head}.*"][0], rest)
            other = by_path.get(where[0]) if where else None
            return res(other, where[1], seen) if other is not None and where is not None else set()

        for m in self.modules:
            for name, (loc, label, source) in m.code.units.items():
                if name not in m.functions:
                    self.units[f"{m.path}::{name}"] = (m, loc, label, source)
        # what each call passes for each parameter of a checked function
        escaped: set[str] = set()
        for m in self.modules:
            for e in m.code.escaped:
                if not e.startswith("param:"):
                    escaped |= res(m, e, set())
        into: dict[tuple[str, str], list[tuple[ir.Module, str]]] = {}
        starred: set[str] = set()
        for m in self.modules:
            for callees, at, targets in m.code.flows:
                for c in callees:
                    for key in res(m, c, set()):
                        if key not in self.funcs:
                            continue
                        params = [p.name for p in self.funcs[key].fn.params]
                        if at == "*":
                            starred.add(key)
                            continue
                        if isinstance(at, str) and at.startswith("^"):  # bound: the receiver fills 'self'
                            at = int(at[1:]) + (1 if params and params[0] in ("self", "cls") else 0)
                        pname = params[at] if isinstance(at, int) and at < len(params) else at if isinstance(at, str) else None
                        if pname is not None:
                            into.setdefault((key, pname), []).extend((m, t) for t in targets)
        for m in self.modules:
            for src, loc, label, targets in m.code.calls:
                keys = set().union(*(res(m, t, set()) for t in targets))
                for k in res(m, src, set()):
                    self.callees.setdefault(k, set()).update(keys)
                    if k in self.funcs:
                        self.code_calls.setdefault(k, []).append((loc, label, keys))
            for e in m.code.escaped:
                self.callees.setdefault(ANY, set()).update(res(m, e, set()))
        for m in self.modules:
            for src, _, _, targets in m.code.later:
                keys = set().union(*(res(m, t, set()) for t in targets))
                for k in res(m, src, set()):
                    self.later.setdefault(k, set()).update(keys - self.callees.get(k, set()))
        for k, keys in self.later.items():
            self.callees.setdefault(k, set()).update(keys)

    def describe(self, key: str) -> str:
        """A function, unit or ``ANY`` as a reader knows it."""
        if key in self.units:
            return self.units[key][2]
        if key == ANY:
            return "a function passed as a value"
        return f"'{ir.source_name(key.split('::')[-1])}'"

    def stack_callees(self, key: str) -> set[str]:
        """What a call of ``key`` may run before it returns."""
        return self.callees.get(key, set()) - self.later.get(key, set())

    def _sccs(self) -> None:
        index: dict[str, int] = {}
        low: dict[str, int] = {}
        stack: list[str] = []
        on: set[str] = set()
        counter = [0]
        comp = [0]

        def strong(v: str) -> None:
            index[v] = low[v] = counter[0]
            counter[0] += 1
            stack.append(v)
            on.add(v)
            for w in self.stack_callees(v):
                if w not in index:
                    strong(w)
                    low[v] = min(low[v], low[w])
                elif w in on:
                    low[v] = min(low[v], index[w])
            if low[v] == index[v]:
                members = []
                while True:
                    w = stack.pop()
                    on.discard(w)
                    self.scc_of[w] = comp[0]
                    members.append(w)
                    if w == v:
                        break
                if len(members) > 1 or v in self.stack_callees(v):
                    self.recursive.update(members)
                comp[0] += 1

        for v in list(self.funcs) + list(self.units) + [ANY]:
            if v not in index:
                strong(v)

    def needs_termination(self, key: str) -> bool:
        """Must recursion through ``key`` be proved to terminate? Always:
        unlike a loop, recursion that never ends crashes (RecursionError in
        Python, RangeError in JavaScript, a stack overflow in Rust), so even
        crash-freedom rests on it."""
        return key in self.recursive

    def same_scc(self, a: str, b: str) -> bool:
        return a in self.recursive and self.scc_of.get(a) == self.scc_of.get(b)

    def _mutation(self) -> None:
        for key, ref in self.funcs.items():
            params = {p.name for p in ref.fn.params if isinstance(p.ty, (ir.TList, ir.TDict))}
            muts: set[str] = set()
            apps: set[str] = set()
            for s in ir.walk_stmts(ref.fn.body):
                if isinstance(s, (ir.IndexAssign, ir.Append, ir.DictDel)) and s.name in params:
                    muts.add(s.name)
                    if isinstance(s, ir.Append):
                        apps.add(s.name)
                for e in ir.stmt_exprs(s):
                    for sub in ir.walk_expr(e):
                        if isinstance(sub, ir.Extern):
                            for a in sub.args:
                                if isinstance(a, ir.Var) and a.name in params:
                                    muts.add(a.name)
                                    apps.add(a.name)
            self.mutated[key] = muts
            self.appends[key] = apps
        # Propagate through calls that pass a list parameter to a mutating callee.
        changed = True
        while changed:
            changed = False
            for key, ref in self.funcs.items():
                params = {p.name for p in ref.fn.params if isinstance(p.ty, (ir.TList, ir.TDict))}
                for s in ir.walk_stmts(ref.fn.body):
                    for e in ir.stmt_exprs(s):
                        for sub in ir.walk_expr(e):
                            if not isinstance(sub, ir.Call):
                                continue
                            tgt = self.resolve(ref.module, sub.func)
                            if tgt is None:
                                continue
                            for p, a in zip(tgt.fn.params, sub.args):
                                if p.name in self.mutated[tgt.key] and isinstance(a, ir.Var) and a.name in params:
                                    if a.name not in self.mutated[key]:
                                        self.mutated[key].add(a.name)
                                        changed = True
                                    if p.name in self.appends[tgt.key] and a.name not in self.appends[key]:
                                        self.appends[key].add(a.name)
                                        changed = True

    def _unchecked_writes(self) -> None:
        """Unchecked values are objects telic models as unchanging terms, so
        anything that may change one must forget what is known about every
        value that may share it: find the views and the writers."""
        direct: set[str] = set()
        for key, ref in self.funcs.items():
            views: set[str] = set()
            for s in ir.walk_stmts(ref.fn.body):
                if isinstance(s, ir.Assign) and _is_view(s.value):
                    views.add(s.name)
                for e in ir.stmt_exprs(s):
                    for sub in ir.walk_expr(e):
                        if isinstance(sub, ir.Builtin) and sub.name == "to_opaque" and isinstance(sub.args[0], ir.Var) and _mutable(sub.args[0].ty):
                            views.add(sub.args[0].name)
            self.views[key] = views
            tys = {**{p.name: p.ty for p in ref.fn.params}, **ref.fn.locals}
            for s in ir.walk_stmts(ref.fn.body):
                if isinstance(s, (ir.IndexAssign, ir.Append, ir.DictDel)) and s.name in views:
                    direct.add(key)
                if isinstance(s, ir.Assign) and in_place(s) and (s.name in views or isinstance(tys.get(s.name), ir.TOpaque)):
                    direct.add(key)
                for e in ir.stmt_exprs(s):
                    for sub in ir.walk_expr(e):
                        if isinstance(sub, ir.Extern) and self.extern_writes_unchecked(sub, ref.fn, views):
                            direct.add(key)
        # calls the code makes (a spec's calls change nothing)
        calls: dict[str, list[tuple[FuncRef, ir.Call]]] = {}
        for key, ref in self.funcs.items():
            calls[key] = []
            for s in ir.walk_stmts(ref.fn.body):
                for e in ir.stmt_exprs(s):
                    for sub in ir.walk_expr(e):
                        tgt = self.resolve(ref.module, sub.func) if isinstance(sub, ir.Call) else None
                        if tgt is not None:
                            calls[key].append((tgt, sub))  # type: ignore[arg-type]
                            if any(p.name in self.mutated.get(tgt.key, ()) and isinstance(a, ir.Var) and a.name in self.views[key] for p, a in zip(tgt.fn.params, sub.args)):  # type: ignore[union-attr]
                                direct.add(key)
        self.unchecked_writers = set(direct)
        changed = True
        while changed:
            changed = False
            for key, cs in calls.items():
                if key not in self.unchecked_writers and any(t.key in self.unchecked_writers for t, _ in cs):
                    self.unchecked_writers.add(key)
                    changed = True

    def _hands_out(self) -> None:
        direct: set[str] = set()
        calls: dict[str, set[str]] = {}
        for key, ref in self.funcs.items():
            calls[key] = set()
            params = {p.name for p in ref.fn.params}
            for s in ir.walk_stmts(ref.fn.body):
                if isinstance(s, ir.FieldAssign) and reaches_class(s.value.ty):
                    direct.add(key)
                # into a container the caller, or unchecked code, may also hold
                if isinstance(s, (ir.Append, ir.IndexAssign)) and reaches_class(s.value.ty) and (s.name in params or s.name in self.views.get(key, set())):
                    direct.add(key)
                for e in ir.stmt_exprs(s):
                    for sub in ir.walk_expr(e):
                        if isinstance(sub, ir.Extern) and any(reaches_class(a.ty) or (isinstance(a.ty, ir.TOpaque) and a.ty.why == "closure") for a in sub.args):
                            direct.add(key)
                        elif isinstance(sub, ir.Builtin) and sub.name in ("to_opaque", "await") and any(reaches_class(a.ty) for a in sub.args):
                            direct.add(key)
                        elif isinstance(sub, ir.Call):
                            tgt = self.resolve(ref.module, sub.func)
                            if tgt is None:
                                direct.add(key)
                            else:
                                calls[key].add(tgt.key)
                        elif isinstance(sub, ir.New):
                            init = self.member(sub.cls, "__init__")
                            if init is not None:
                                calls[key].add(init.key)
        self.hands_out = set(direct)
        changed = True
        while changed:
            changed = False
            for key, cs in calls.items():
                if key not in self.hands_out and cs & self.hands_out:
                    self.hands_out.add(key)
                    changed = True

    def python_only(self, key: str) -> bool:
        """Only the Python core unfolds trusted predicates and forgets what
        a change to an unchecked value may have broken."""
        return key in self.predicate_users or key in self.unchecked_writers

    def extern_writes_unchecked(self, e: ir.Extern, fn: ir.Function, views: set[str], bound: set[str] | None = None) -> bool:
        """May this unchecked call change an object an unchecked value can
        reach? Only through what it is handed (a closure may reach whatever
        the function holds: its variables, or those ``bound`` now), and not
        if it only reads."""
        if any(isinstance(a.ty, ir.TOpaque) and a.ty.why == "closure" for a in e.args):
            tys = {**{p.name: p.ty for p in fn.params}, **fn.locals}
            return any(reaches_unchecked(t) for n, t in tys.items() if bound is None or n in bound)
        if e.name.split(".")[-1] in PURE_EXTERNS or unchecked_constructor(e):
            return False
        return any(_hands_unchecked(a, views) for a in e.args)

    def _heap(self) -> None:
        """Which fields each function may write (and of which objects), which
        it reads, and whether it allocates; transitively through calls."""
        params = {k: {p.name for p in r.fn.params} for k, r in self.funcs.items()}
        direct_w: dict[str, dict[str, set[str]]] = {}
        direct_r: dict[str, set[str]] = {}
        calls: dict[str, list[tuple[str, tuple[ir.Expr, ...], bool]]] = {}
        for key, ref in self.funcs.items():
            w: dict[str, set[str]] = {}
            r: set[str] = set()
            cs: list[tuple[str, tuple[ir.Expr, ...], bool]] = []
            exprs: list[ir.Expr] = []
            for st in ir.walk_stmts(ref.fn.body):
                if isinstance(st, ir.FieldAssign):
                    tgt = st.obj.name if isinstance(st.obj, ir.Var) and st.obj.name in params[key] else "*"
                    w.setdefault(f"{st.cls}.{st.field}", set()).add(tgt)
                exprs.extend(ir.stmt_exprs(st))
                if isinstance(st, (ir.While, ir.ForRange, ir.ForEach)):
                    exprs.extend(c.expr for c in st.invariants)
            for c in ref.fn.requires + ref.fn.ensures:
                exprs.append(c.expr)
            for e in exprs:
                for sub in ir.walk_expr(e):
                    if isinstance(sub, ir.Field) and isinstance(sub.obj.ty, ir.TClass):
                        r.add(f"{sub.obj.ty.name}.{sub.name}")
                    elif isinstance(sub, ir.Call):
                        tgt = self.resolve(ref.module, sub.func)
                        if tgt is not None:
                            cs.append((tgt.key, sub.args, False))
                    elif isinstance(sub, ir.Extern) and self.extern_touches_heap(sub):
                        self.allocates.add(key)
                        for cname, decl in self.classes.items():
                            for fname, _ in decl.fields:
                                w.setdefault(f"{cname}.{fname}", set()).add("*")
                    elif isinstance(sub, ir.New):
                        self.allocates.add(key)
                        init = self.member(sub.cls, "__init__")
                        if init is not None:
                            cs.append((init.key, sub.args, True))
                        else:
                            decl = self.classes.get(sub.cls)
                            for fname, _ in decl.fields if decl else []:
                                w.setdefault(f"{sub.cls}.{fname}", set()).add("@new")
                            post = self.member(sub.cls, "__post_init__")
                            if post is not None:
                                cs.append((post.key, (), True))
            direct_w[key], direct_r[key], calls[key] = w, r, cs
        self.heap_writes = {k: {f: set(t) for f, t in v.items()} for k, v in direct_w.items()}
        self.heap_reads = {k: set(v) for k, v in direct_r.items()}
        changed = True
        while changed:
            changed = False
            for key, cs in calls.items():
                mine = self.heap_writes[key]
                for callee, args, is_new in cs:
                    if callee in self.allocates and key not in self.allocates:
                        self.allocates.add(key)
                        changed = True
                    for rf in self.heap_reads.get(callee, set()) - self.heap_reads[key]:
                        self.heap_reads[key].add(rf)
                        changed = True
                    cparams = [p.name for p in self.funcs[callee].fn.params]
                    if is_new:
                        cparams = cparams[1:]  # 'self' is the fresh object
                    for f, tgts in list(self.heap_writes.get(callee, {}).items()):
                        for t in list(tgts):
                            if t in ("*", "@new"):
                                mapped = t
                            elif is_new and t == "self":
                                mapped = "@new"
                            elif t in cparams:
                                a = args[cparams.index(t)]
                                mapped = a.name if isinstance(a, ir.Var) and a.name in params[key] else "*"
                            else:
                                mapped = "*"
                            if mapped not in mine.setdefault(f, set()):
                                mine[f].add(mapped)
                                changed = True

    def extern_touches_heap(self, e: ir.Extern) -> bool:
        """Can this unchecked call reach checked objects? Only through what
        it is handed: objects, containers, or opaque values (which may hold
        objects handed out earlier)."""
        if not self.classes:
            return False

        def reach(t: ir.Type) -> bool:
            if isinstance(t, (ir.TClass, ir.TOpaque)):
                return True
            if isinstance(t, ir.TList):
                return reach(t.elem)
            if isinstance(t, ir.TDict):
                return reach(t.val)
            if isinstance(t, ir.TOption):
                return reach(t.inner)
            return False

        return any(reach(a.ty) for a in e.args)

    def def_heap_keys(self, key: str) -> list[str]:
        """Heap components a definitional function's body reads, in a fixed
        order; they become extra parameters of its logical definition."""
        from .vcgen import components

        out = []
        for cf in sorted(self.heap_reads.get(key, ())):
            c, f = cf.split(".", 1)
            decl = self.classes.get(c)
            fty = decl.field_type(f) if decl else None
            if fty is None:
                continue
            for suffix, _ in components(fty):
                out.append(f"@{decl.field_owner(f)}.{f}" + (f".{suffix}" if suffix else ""))
        return out

    def _predicates(self) -> None:
        scalar = (ir.TBool, ir.TInt, ir.TReal, ir.TStr)
        for key, ref in self.funcs.items():
            fn = ref.fn
            if fn.trusted and fn.ensures and isinstance(fn.ret, scalar) and not any(isinstance(p.ty, ir.TClass) for p in fn.params):
                self.predicates.add(key)
        if not self.predicates:
            return
        direct = {k for k, cs in self.callees.items() if cs & self.predicates}
        self.predicate_users = direct | {k for k, cs in self.callees.items() if cs & direct}

    def _definitional(self) -> None:
        """A function is definitional if its body is loop-free, mutation-free,
        free of raises, and only calls other definitional functions. Its body
        then *is* a logical definition, so specs may call it."""
        cand: set[str] = set()
        for key, ref in self.funcs.items():
            fn = ref.fn
            if fn.unsupported or fn.trusted or fn.ret == ir.NONE or isinstance(fn.ret, (ir.TList, ir.TOption, ir.TDict)):
                continue
            if key in self.allocates or fn.name.endswith(".__init__") or key in self.dispatch:
                continue  # an overridden method's body is not what every call runs
            if self.ambiguity(ref) is not None:
                continue
            if any(isinstance(sub, ir.Extern) for st in ir.walk_stmts(fn.body) for e in ir.stmt_exprs(st) for sub in ir.walk_expr(e)):
                continue
            ok = True
            for s in ir.walk_stmts(fn.body):
                if isinstance(s, (ir.While, ir.ForRange, ir.ForEach, ir.IndexAssign, ir.Append, ir.Raise, ir.Break, ir.Continue, ir.ExprStmt, ir.Unsupported, ir.AssumeStmt, ir.FieldAssign, ir.DictDel)):
                    ok = False
                    break
            if ok:
                cand.add(key)
        changed = True
        while changed:
            changed = False
            for key in list(cand):
                if not self.callees[key] <= cand | self.predicates:
                    cand.discard(key)
                    changed = True
        self.definitional = cand

    def _names(self) -> None:
        by_name: dict[str, list[str]] = {}
        for key, ref in self.funcs.items():
            by_name.setdefault(ref.fn.name, []).append(key)
        used: set[str] = set()
        for name, keys in by_name.items():
            for key in keys:
                if len(keys) == 1 and not name.startswith(("seqsum", "seqcount", "Telic")):
                    cand = re.sub(r"\W", "_", name)
                else:
                    stem = re.sub(r"\W", "_", self.funcs[key].module.path.rsplit("/", 1)[-1])
                    cand = f"{stem}_{name}"
                base, k = cand, 1
                while cand in used:
                    k += 1
                    cand = f"{base}_{k}"
                used.add(cand)
                self.logic_names[key] = cand


# ---------------------------------------------------------------------------
# Classes with the same name in several checked files


def qualify_classes(modules: list[ir.Module]) -> None:
    """Give each class that several checked files define a module-qualified
    name (``Lowerer@rust``) everywhere it is meant: in the module defining
    it and in modules importing it. Functions are renamed with their class
    (``Lowerer@rust.run``). Names a module uses that cannot be attributed
    to one definition (it neither defines nor imports them, or a
    declaration it borrows from another file means a different one) are
    recorded in its ``ambiguous_classes``."""
    defs: dict[str, list[ir.Module]] = {}
    for m in modules:
        for cname in m.classes:
            defs.setdefault(cname, []).append(m)
    dup = {c: ms for c, ms in defs.items() if len(ms) > 1}
    if not dup:
        return
    qual: dict[tuple[int, str], str] = {}
    for cname, ms in dup.items():
        for m, tag in zip(ms, _tags([m.path for m in ms])):
            qual[(id(m), cname)] = f"{cname}@{tag}"
    by_path = {m.path: m for m in modules}
    views: dict[int, dict[str, str]] = {}
    for m in modules:
        v: dict[str, str] = {}
        for cname in dup:
            if cname in m.classes:
                v[cname] = qual[(id(m), cname)]
            elif cname in m.class_origin and m.class_origin[cname] in by_path:
                q = qual.get((id(by_path[m.class_origin[cname]]), cname))
                if q is not None:
                    v[cname] = q
        views[id(m)] = v
    fn_home = {(m.path, name): m for m in modules for name in m.functions}
    in_records = {n for m in modules for r in m.records.values() for n in _class_names(r) if n in dup}
    out: dict[str, dict[str, str]] = {}
    for m in modules:
        v = views[id(m)]
        bad: dict[str, str] = {}
        for cname in dup:
            if cname not in v:
                bad[cname] = f"class {cname} is defined in {' and '.join(x.path for x in dup[cname])}, and {m.path} neither defines nor imports it, so telic cannot tell which one is meant (import it explicitly)"
            elif cname in in_records:
                bad[cname] = f"a record type mentions class {cname}, which several checked files define; telic cannot tell which one is meant"
        # Declarations lowered into this module from elsewhere keep their
        # home's meaning of a name; where that differs from this module's,
        # the name is ambiguous here.
        borrowed: list[tuple[ir.Module, object]] = []
        for cname, path in m.class_origin.items():
            src = by_path.get(path)
            if src is not None and cname in src.classes:
                borrowed.append((src, src.classes[cname].fields))
        used = set(re.findall(r"TClass\(name='([^']+)'\)", repr(list(m.functions.values())) + repr(list(m.classes.values()))))
        for src in modules:
            if src is not m:
                borrowed += [(src, d.fields) for c, d in src.classes.items() if c not in dup and c in used]
        for _, (path, remote) in m.imports.items():
            src = fn_home.get((path, remote))
            if src is not None and src is not m:
                f = src.functions[remote]
                borrowed.append((src, (f.params, f.ret)))
        for src, what in borrowed:
            for n in _class_names(what):
                if n in dup and n not in bad and views[id(src)].get(n) != v.get(n):
                    bad[n] = f"class {n} is defined in {' and '.join(x.path for x in dup[n])}, and a declaration {m.path} uses from {src.path} means a different one than {m.path} does; telic cannot tell them apart here"
        if bad:
            out[m.path] = bad
    for m in modules:
        v = {c: q for c, q in views[id(m)].items() if c not in out.get(m.path, {})}
        if v:
            _rename(m, v)
        m.ambiguous_classes.update(out.get(m.path, {}))


def _tags(paths: list[str]) -> list[str]:
    """Shortest distinguishing path suffixes: a/x.py, b/x.py -> a_x, b_x."""
    parts = [re.sub(r"\.\w+$", "", p).split("/") for p in paths]
    for k in range(1, max(len(x) for x in parts) + 1):
        tags = [re.sub(r"\W", "_", "_".join(x[-k:])) for x in parts]
        if len(set(tags)) == len(tags):
            return tags
    return [f"{t}_{i + 1}" for i, t in enumerate(tags)]


def _class_names(x: object) -> set[str]:
    out: set[str] = set()

    def walk(y: object) -> None:
        if isinstance(y, ir.TClass):
            out.add(y.name)
        elif isinstance(y, (list, tuple)):
            for z in y:
                walk(z)
        elif isinstance(y, (ir.TList, ir.TOption, ir.TDict, ir.TRecord, ir.Param)):
            for f in dataclasses.fields(y):
                walk(getattr(y, f.name))

    walk(x)
    return out


def _rename(m: ir.Module, view: dict[str, str]) -> None:
    def name(n: str) -> str:
        head, dot, rest = n.partition(".")
        return view[head] + dot + rest if head in view else n

    def rw(x):
        if isinstance(x, ir.TClass):
            return ir.TClass(view[x.name]) if x.name in view else x
        if isinstance(x, list):
            return [rw(y) for y in x]
        if isinstance(x, tuple):
            ys = tuple(rw(y) for y in x)
            return x if all(a is b for a, b in zip(x, ys)) else ys
        if isinstance(x, (ir.Loc, ir.TRecord, str)) or not dataclasses.is_dataclass(x):
            return x
        changes = {}
        for f in dataclasses.fields(x):
            old = getattr(x, f.name)
            new = name(old) if f.name in ("cls", "func") and isinstance(old, str) and isinstance(x, (ir.New, ir.FieldAssign, ir.Call)) else rw(old)
            if new is not old:
                changes[f.name] = new
        return dataclasses.replace(x, **changes) if changes else x

    fns = {}
    for key, fn in m.functions.items():
        fn.name = name(fn.name)
        fn.params = rw(fn.params)
        fn.ret = rw(fn.ret)
        fn.requires, fn.ensures, fn.raises = rw(fn.requires), rw(fn.ensures), rw(fn.raises)
        fn.decreases = rw(fn.decreases)
        fn.body = rw(fn.body)
        fn.locals = {k: rw(t) for k, t in fn.locals.items()}
        fns[name(key)] = fn
    m.functions = fns
    classes = {}
    for cname, decl in m.classes.items():
        decl.name = name(decl.name)
        decl.fields = [(f, rw(t)) for f, t in decl.fields]
        decl.invariants = rw(decl.invariants)
        decl.lifecycles = rw(decl.lifecycles)
        decl.bases = [name(b) for b in decl.bases]
        decl.owner = {f: name(o) for f, o in decl.owner.items()}
        classes[name(cname)] = decl
    m.classes = classes
    m.class_origin = {name(c): p for c, p in m.class_origin.items()}


def _escapes_of_self(body: list[ir.Stmt]) -> list[ir.Expr]:
    """Expressions that hand ``self`` on (anything but reading or writing
    one of its fields, or running a base constructor on it)."""
    out: list[ir.Expr] = []

    def visit(e: ir.Expr, parent: ir.Expr | None) -> None:
        if isinstance(e, ir.Var) and e.name == "self":
            if isinstance(parent, ir.Field) or (isinstance(parent, ir.Call) and parent.func.endswith(".__init__") and parent.args[:1] == (e,)):
                return
            out.append(parent or e)
            return
        for sub in ir.walk_expr(e):
            if sub is not e and _child(e, sub):
                visit(sub, e)

    for s in ir.walk_stmts(body):
        for e in ir.stmt_exprs(s):
            if isinstance(s, ir.FieldAssign) and e is s.obj and isinstance(e, ir.Var):
                continue
            visit(e, None)
    return out


def _child(e: ir.Expr, sub: ir.Expr) -> bool:
    """Is ``sub`` an immediate sub-expression of ``e``?"""
    for f in dataclasses.fields(e):
        v = getattr(e, f.name)
        if v is sub or (isinstance(v, tuple) and any(x is sub or (isinstance(x, tuple) and sub in x) for x in v)):
            return True
    return False


def _rewrite_expr(e: Any, f, parent: ir.Expr | None = None) -> Any:
    """``e`` with every sub-expression ``x`` for which ``f(x, parent)``
    returns a replacement replaced (children first)."""
    if isinstance(e, tuple):
        return tuple(_rewrite_expr(x, f, parent) for x in e)
    if not isinstance(e, ir.Expr):
        return e
    changes = {}
    for fl in dataclasses.fields(e):
        v = getattr(e, fl.name)
        if isinstance(v, (ir.Expr, tuple)):
            nv = _rewrite_expr(v, f, e)
            if nv is not v:
                changes[fl.name] = nv
    out = dataclasses.replace(e, **changes) if changes else e
    return f(out, parent) or out


def _rewrite_stmts(stmts: list[ir.Stmt], f) -> list[ir.Stmt]:
    out = []
    for s in stmts:
        changes = {}
        for fl in dataclasses.fields(s):
            v = getattr(s, fl.name)
            if isinstance(v, ir.Expr):
                nv = _rewrite_expr(v, f)
            elif isinstance(v, list) and all(isinstance(x, ir.Stmt) for x in v):
                nv = _rewrite_stmts(v, f)
            elif isinstance(v, tuple) and v and all(isinstance(x, list) for x in v):
                nv = tuple(_rewrite_stmts(x, f) for x in v)
            else:
                continue
            if nv != v:
                changes[fl.name] = nv
        out.append(dataclasses.replace(s, **changes) if changes else s)
    return out


# Unchecked calls that only read what they are handed (the last part of the name).
PURE_EXTERNS = frozenset(
    "get keys values items entries copy count index find rfind startswith endswith startsWith endsWith lower upper "
    "toLowerCase toUpperCase strip lstrip rstrip trim split rsplit splitlines join format replace encode decode "
    "isdigit isalpha isalnum isspace print log warn error str repr String Number Boolean len int float bool "
    "isinstance type id hash sorted list dict tuple set frozenset dumps stringify abs min max sum any all round "
    "isArray isInteger isNaN parseInt parseFloat slice concat indexOf lastIndexOf includes at toString "
    "hasOwnProperty charAt charCodeAt substring padStart padEnd repeat getattr hasattr chr ord from_bytes".split()
)


# Operations on unchecked values whose result is a new object.
FRESH_OPS = frozenset("add mult comprehension dict tuple set array object rest slice_step".split())


def in_place(s: ir.Assign) -> bool:
    """``xs += ys`` and the like: Python changes a list, set or dict in place."""
    v = s.value
    if isinstance(v, ir.Builtin) and v.name == "list_concat":
        first = v.args[0]
    elif isinstance(v, ir.Builtin) and v.name == "opaque_op" and isinstance(v.args[0], ir.Lit) and v.args[0].value in ("add", "mult", "sub", "bitor", "bitand", "bitxor") and len(v.args) > 1:
        first = v.args[1]
    else:
        return False
    return isinstance(first, ir.Var) and first.name == s.name


def unchecked_constructor(e: ir.Extern) -> bool:
    """``Name(...)`` or ``new Name(...)``: assumed to leave what it is handed unchanged."""
    last = e.name.removeprefix("new ").split(".")[-1]
    return last[:1].isupper()


def reaches_class(t: ir.Type) -> bool:
    """Can a value of type ``t`` hold (or be) a checked object?"""
    if isinstance(t, ir.TClass):
        return True
    if isinstance(t, ir.TList):
        return reaches_class(t.elem)
    if isinstance(t, ir.TDict):
        return reaches_class(t.val)
    if isinstance(t, ir.TOption):
        return reaches_class(t.inner)
    if isinstance(t, ir.TRecord):
        return any(reaches_class(ft) for _, ft in t.fields)
    return False


def reaches_unchecked(t: ir.Type) -> bool:
    """Can a value of type ``t`` hold (or be) an unchecked object?"""
    if isinstance(t, ir.TOpaque):
        return True
    if isinstance(t, ir.TList):
        return reaches_unchecked(t.elem)
    if isinstance(t, ir.TDict):
        return reaches_unchecked(t.val)
    if isinstance(t, ir.TOption):
        return reaches_unchecked(t.inner)
    if isinstance(t, ir.TRecord):
        return any(reaches_unchecked(ft) for _, ft in t.fields)
    return False


def _hands_unchecked(a: ir.Expr, views: set[str]) -> bool:
    """Does passing ``a`` hand over an unchecked object? A checked value seen
    untyped holds none."""
    if isinstance(a, ir.Builtin) and a.name == "to_opaque":
        return _hands_unchecked(a.args[0], views)
    return reaches_unchecked(a.ty) or (isinstance(a, ir.Var) and a.name in views)


def _mutable(t: ir.Type) -> bool:
    return isinstance(t.inner if isinstance(t, ir.TOption) else t, (ir.TList, ir.TDict))


def _is_view(e: ir.Expr) -> bool:
    """Does ``e`` denote an unchecked object seen at a checked container type?"""
    if isinstance(e, ir.Builtin) and e.name == "from_opaque":
        x = e.args[0]
        new = isinstance(x, ir.Builtin) and (x.name == "each" or (x.name == "opaque_op" and isinstance(x.args[0], ir.Lit) and x.args[0].value in FRESH_OPS))
        return _mutable(e.ty) and not new
    if isinstance(e, ir.Builtin) and e.name in ("some", "await"):
        return _is_view(e.args[0])
    if isinstance(e, ir.Ite):
        return _is_view(e.then) or _is_view(e.orelse)
    return False
