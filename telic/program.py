"""Whole-program facts the verifier needs: name resolution, the call graph,
recursion SCCs, which functions are *definitional* (usable inside specs), and
which list parameters a function mutates."""

from __future__ import annotations

import dataclasses
import re
from dataclasses import dataclass, field

from . import ir


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
    mutated: dict[str, set[str]] = field(default_factory=dict)
    appends: dict[str, set[str]] = field(default_factory=dict)
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

    @classmethod
    def build(cls, modules: list[ir.Module]) -> "Program":
        p = cls(modules)
        qualify_classes(modules)
        p.ambiguous = {m.path: dict(m.ambiguous_classes) for m in modules if m.ambiguous_classes}
        for m in modules:
            for f in m.functions.values():
                ref = FuncRef(m, f)
                p.funcs[ref.key] = ref
        for m in modules:
            for cname, decl in m.classes.items():
                p.classes[cname] = decl
                p.class_module[cname] = m
        p._overrides()
        p._call_graph()
        p._sccs()
        p._mutation()
        p._heap()
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
        return out

    def _call_graph(self) -> None:
        for key, ref in self.funcs.items():
            self.callees[key] = self._calls_in(ref)

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
            for w in self.callees.get(v, ()):
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
                if len(members) > 1 or v in self.callees.get(v, ()):
                    self.recursive.update(members)
                comp[0] += 1

        for v in self.funcs:
            if v not in index:
                strong(v)

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
                    for f, tgts in self.heap_writes.get(callee, {}).items():
                        for t in tgts:
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
                if not self.callees[key] <= cand:
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
        decl.bases = [name(b) for b in decl.bases]
        decl.owner = {f: name(o) for f, o in decl.owner.items()}
        classes[name(cname)] = decl
    m.classes = classes
    m.class_origin = {name(c): p for c, p in m.class_origin.items()}
