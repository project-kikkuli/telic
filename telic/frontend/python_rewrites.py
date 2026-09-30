"""Where Python code can tie a frozen dataclass or NamedTuple into a knot:
rewrite an object (``object.__setattr__``, ``setattr``, ``vars``, writing
through ``__dict__``, assigning ``__class__``) or subclass a class somewhere
telic does not model (inside a function, with ``type(name, bases, ns)``).
Each site names the classes it can reach when the code says statically,
else None: any class."""

from __future__ import annotations

import ast

_ANY = {"Any", "object", "tuple", "Tuple", "NamedTuple", "type", "Type"}
_WRAPPERS = {"Optional", "Union", "Final", "ClassVar", "Annotated"}
_DICT_WRITES = {"update", "setdefault", "pop", "popitem", "clear", "__setitem__", "__delitem__"}


def _last(e: ast.expr) -> str | None:
    if isinstance(e, ast.Name):
        return e.id
    if isinstance(e, ast.Attribute):
        return e.attr
    return None


def rewrites(tree: ast.Module, classes: set[str], foreign: bool) -> list[tuple[str, set[str] | None]]:
    """(kind, class names) for every site in ``tree``: kind ``obj`` rewrites
    an object of those classes (or a subclass), ``sub`` subclasses them
    (``foreign``: its top-level classes count, as the tree is another
    module's). ``classes`` are the checked classes of the project; names are
    as the defining module spells them (import aliases undone)."""
    alias: dict[str, str] = {}
    types: dict[str, ast.expr] = {}
    for node in tree.body:
        if isinstance(node, ast.ImportFrom):
            for a in node.names:
                alias[a.asname or a.name] = a.name
        elif isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
            types[node.targets[0].id] = node.value
    known = classes | {n.name for n in tree.body if isinstance(n, ast.ClassDef)}

    def name(n: str) -> str:
        return alias.get(n, n)

    def annotated(a: ast.expr | None, seen: frozenset[str] = frozenset()) -> set[str] | None:
        if a is None:
            return None
        if isinstance(a, ast.Constant) and isinstance(a.value, str):
            try:
                return annotated(ast.parse(a.value, mode="eval").body, seen)
            except SyntaxError:
                return None
        if isinstance(a, ast.Constant) and a.value is None:
            return set()
        if isinstance(a, ast.BinOp) and isinstance(a.op, ast.BitOr):
            left, right = annotated(a.left, seen), annotated(a.right, seen)
            return None if left is None or right is None else left | right
        if isinstance(a, ast.Subscript) and _last(a.value) in _WRAPPERS:
            parts = a.slice.elts if isinstance(a.slice, ast.Tuple) else [a.slice]
            out: set[str] = set()
            for p in parts:
                got = annotated(p, seen)
                if got is None:
                    return None
                out |= got
            return out
        n = _last(a.value if isinstance(a, ast.Subscript) else a)
        if n is None or n in _ANY:
            return None
        if n in types and n not in seen and isinstance(a, ast.Name):
            return annotated(types[n], seen | {n})
        return {name(n)}

    def static(e: ast.expr, fn: ast.FunctionDef | ast.AsyncFunctionDef | None, cls: str | None) -> set[str] | None:
        """The classes ``e`` can be an instance of (or of a subclass), or None."""
        if isinstance(e, ast.Call) and isinstance(e.func, ast.Name) and e.func.id == "super":
            return {cls} if cls else None
        if isinstance(e, ast.Call) and _last(e.func) in known:
            return {name(_last(e.func) or "")}
        if not isinstance(e, ast.Name) or fn is None:
            return None
        args = fn.args.posonlyargs + fn.args.args
        if cls and args and e.id == args[0].arg and not any(_last(d) in ("staticmethod", "classmethod") for d in fn.decorator_list):
            return {cls}
        for a in args + fn.args.kwonlyargs:
            if a.arg == e.id:
                return annotated(a.annotation)
        out: set[str] = set()
        for n in _walk_own(fn):
            if isinstance(n, (ast.Assign, ast.AnnAssign, ast.AugAssign, ast.NamedExpr)):
                targets = n.targets if isinstance(n, ast.Assign) else [n.target]
                if any(isinstance(t, ast.Name) and t.id == e.id for t in targets):
                    got = static(n.value, None, cls) if n.value is not None and not isinstance(n, ast.AugAssign) else None
                    if got is None:
                        return None
                    out |= got
            elif isinstance(n, (ast.For, ast.AsyncFor, ast.With, ast.AsyncWith, ast.comprehension, ast.ExceptHandler, ast.Global, ast.Nonlocal)):
                bound = n.names if isinstance(n, (ast.Global, ast.Nonlocal)) else [n.name] if isinstance(n, ast.ExceptHandler) else [x.id for t in _bound_targets(n) for x in ast.walk(t) if isinstance(x, ast.Name)]
                if e.id in bound:
                    return None
        return out or None

    out: list[tuple[str, set[str] | None]] = []
    top = set(map(id, tree.body))

    def visit(node: ast.AST, fn, cls: str | None, parent: ast.AST | None) -> None:
        if isinstance(node, ast.ClassDef):
            if foreign or id(node) not in top:
                out.append(("sub", {name(b) for b in (_last(x) for x in node.bases) if b}))
            for d in node.decorator_list + node.bases + [k.value for k in node.keywords]:
                visit(d, fn, cls, node)
            for st in node.body:
                visit(st, fn if id(node) not in top else None, node.name, node)
            return
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            for d in node.decorator_list:
                visit(d, fn, cls, node)
            for st in node.body:
                visit(st, node, cls if isinstance(parent, ast.ClassDef) else None, node)
            return
        if isinstance(node, ast.Call):
            f = node.func
            first = node.args[0] if node.args else None
            if isinstance(f, ast.Name) and f.id in ("setattr", "vars") and first is not None:
                out.append(("obj", static(first, fn, cls)))
            elif isinstance(f, ast.Name) and f.id == "type" and len(node.args) == 3:
                bases = node.args[1]
                names = [_last(b) for b in bases.elts] if isinstance(bases, ast.Tuple) else [None]
                out.append(("sub", None if None in names else {name(b) for b in names if b}))
            elif isinstance(f, ast.Attribute) and f.attr == "__setattr__":
                if isinstance(f.value, ast.Name) and f.value.id == "object":
                    out.append(("obj", static(first, fn, cls) if first is not None else None))
                else:
                    out.append(("obj", static(f.value, fn, cls)))
            for c in [f] + node.args + [k.value for k in node.keywords]:
                if isinstance(c, ast.Attribute) and c.attr == "__setattr__" and c is not f:
                    out.append(("obj", None))  # the method itself handed to other code
                elif isinstance(c, ast.Name) and c.id == "setattr" and c is not f:
                    out.append(("obj", None))
                visit(c, fn, cls, node)
            return
        if isinstance(node, ast.Attribute):
            if node.attr == "__class__" and isinstance(node.ctx, ast.Store):
                target = static(node.value, fn, cls)
                value = parent.value if isinstance(parent, ast.Assign) else None
                new = {name(value.id)} if isinstance(value, ast.Name) else None
                out.append(("obj", None if target is None or new is None else target | new))
            elif node.attr == "__dict__" and _writes_dict(node, parent):
                out.append(("obj", static(node.value, fn, cls)))
            visit(node.value, fn, cls, node)
            return
        for c in ast.iter_child_nodes(node):
            visit(c, fn, cls, node)

    for st in tree.body:
        visit(st, None, None, tree)
    return out


def _writes_dict(node: ast.Attribute, parent: ast.AST | None) -> bool:
    """Is ``x.__dict__`` written, or handed to code that may write it?
    Reading it (``.items()``, ``.get(k)``, iterating) is not."""
    if isinstance(node.ctx, (ast.Store, ast.Del)):
        return True
    if isinstance(parent, ast.Attribute) and parent.value is node:
        return parent.attr in _DICT_WRITES
    if isinstance(parent, ast.Subscript) and parent.value is node:
        return not isinstance(parent.ctx, ast.Load)
    if isinstance(parent, (ast.comprehension, ast.For, ast.Compare)):
        return False
    if isinstance(parent, ast.Call) and _last(parent.func) in ("len", "list", "sorted", "dict", "repr", "str", "iter"):
        return False
    return True


def _bound_targets(n: ast.AST) -> list[ast.expr]:
    if isinstance(n, (ast.For, ast.AsyncFor, ast.comprehension)):
        return [n.target]
    if isinstance(n, (ast.With, ast.AsyncWith)):
        return [i.optional_vars for i in n.items if i.optional_vars is not None]
    return []


def _walk_own(fn: ast.AST):
    """Nodes of a function body, not descending into nested defs, classes or lambdas."""
    stack = list(ast.iter_child_nodes(fn))
    while stack:
        n = stack.pop()
        yield n
        if not isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef, ast.Lambda)):
            stack.extend(ast.iter_child_nodes(n))
