"""A Rust crate's module tree: the file each module lives in (``mod x;``),
what each module declares, and how paths (``crate::a::B``, ``super::f``,
``use`` aliases and globs, ``Enum::Variant``) resolve to those declarations.

The crate root is ``src/lib.rs`` or ``src/main.rs`` next to the nearest
``Cargo.toml`` when the file is reachable from it; otherwise the file is its
own root."""

from __future__ import annotations

import os
from dataclasses import dataclass, field
from typing import Any

ModPath = tuple[str, ...]

ITEM_KINDS = {
    "struct_item": "struct",
    "enum_item": "enum",
    "trait_item": "trait",
    "function_item": "fn",
    "function_signature_item": "fn",
    "const_item": "const",
    "static_item": "static",
    "type_item": "type",
    "union_item": "union",
}


def _text(n: Any) -> str:
    return n.text.decode("utf8")


@dataclass
class Item:
    kind: str  # struct | enum | trait | fn | const | static | type | union | impl
    name: str
    mod: ModPath
    node: Any
    file: str
    attrs: list[str] = field(default_factory=list)


@dataclass
class ModInfo:
    path: ModPath
    file: str
    items: dict[str, list[Item]] = field(default_factory=dict)  # by name; several under cfg variants
    impls: list[Item] = field(default_factory=list)
    children: dict[str, ModPath] = field(default_factory=dict)
    uses: dict[str, list[str]] = field(default_factory=dict)  # alias -> path segments
    globs: list[list[str]] = field(default_factory=list)


@dataclass(frozen=True)
class Res:
    """What a path names: a module, an item, or a member of one (an enum's
    variant, a type's associated function)."""

    kind: str  # mod | item | variant | assoc
    mod: ModPath = ()
    item: Item | None = None
    member: str = ""


class Crate:
    def __init__(self, root_file: str, sources: dict[str, str] | None = None):
        self.root_file = root_file
        self.sources: dict[str, str] = {}
        self.trees: dict[str, Any] = {}
        self.mods: dict[ModPath, ModInfo] = {}
        self.problems: list[tuple[str, str, int]] = []  # (file, message, line)
        self._given = sources or {}
        self._load(root_file, ())

    # -- building -----------------------------------------------------------

    def _read(self, path: str) -> str | None:
        if path in self._given:
            return self._given[path]
        try:
            with open(path, encoding="utf8") as f:
                return f.read()
        except OSError:
            return None

    def _load(self, file: str, mod: ModPath) -> None:
        from .rust import parser

        src = self._read(file)
        if src is None:
            return
        self.sources[file] = src
        tree = parser().parse(src.encode("utf8"))
        self.trees[file] = tree
        self._module(tree.root_node, file, mod, self._child_dir(file, mod))

    def _child_dir(self, file: str, mod: ModPath) -> str:
        """Where 'mod x;' in this file looks for x.rs: next to a root or
        mod.rs file, in a directory named after the module otherwise."""
        d = os.path.dirname(file)
        base = os.path.basename(file)
        if not mod or base == "mod.rs" or file == self.root_file:
            return d
        return os.path.join(d, os.path.splitext(base)[0])

    def _module(self, container: Any, file: str, mod: ModPath, child_dir: str) -> None:
        info = self.mods.setdefault(mod, ModInfo(mod, file))
        attrs: list[str] = []
        for c in container.children:
            if c.type == "attribute_item":
                attrs.append(_text(c))
                continue
            if c.type in ("line_comment", "block_comment") or not c.is_named:
                continue
            here, attrs = attrs, []
            if any("cfg(test)" in a for a in here):
                continue
            if c.type == "mod_item":
                name = _text(c.child_by_field_name("name"))
                sub = mod + (name,)
                info.children[name] = sub
                body = c.child_by_field_name("body")
                if body is not None:
                    self._module(body, file, sub, os.path.join(child_dir, name))
                    continue
                target = self._mod_file(child_dir, name, here, file)
                if target is None:
                    self.problems.append((file, f"mod {name}: no file {name}.rs or {name}/mod.rs; its items are unknown", c.start_point[0] + 1))
                    continue
                if target in self.sources:
                    continue
                self._load(target, sub)
                continue
            if c.type == "use_declaration":
                arg = c.child_by_field_name("argument")
                for alias, segs in _use_tree(_text(arg) if arg is not None else ""):
                    if alias == "*":
                        info.globs.append(segs)
                    else:
                        info.uses[alias] = segs
                continue
            if c.type == "impl_item":
                info.impls.append(Item("impl", "", mod, c, file, here))
                continue
            kind = ITEM_KINDS.get(c.type)
            if kind is None:
                continue
            nm = c.child_by_field_name("name")
            if nm is None:
                continue
            info.items.setdefault(_text(nm), []).append(Item(kind, _text(nm), mod, c, file, here))

    def _mod_file(self, child_dir: str, name: str, attrs: list[str], file: str) -> str | None:
        for a in attrs:
            if a.startswith("#[path"):
                q = a.split("=", 1)[-1].strip().rstrip("]").strip().strip('"')
                p = os.path.normpath(os.path.join(os.path.dirname(file), q))
                return p if self._read(p) is not None else None
        for p in (os.path.join(child_dir, f"{name}.rs"), os.path.join(child_dir, name, "mod.rs")):
            if self._read(p) is not None:
                return os.path.normpath(p)
        return None

    # -- queries --------------------------------------------------------------

    def modules_in(self, file: str) -> list[ModPath]:
        return [m for m, i in self.mods.items() if i.file == file]

    def all_items(self) -> list[Item]:
        return [it for m in self.mods.values() for its in m.items.values() for it in its]

    def resolve(self, mod: ModPath, segs: list[str], seen: set | None = None) -> Res | None:
        """What ``a::b::c`` means inside module ``mod`` (None: outside the crate)."""
        if not segs:
            return None
        seen = set() if seen is None else seen
        first, rest = segs[0], segs[1:]
        if first == "crate":
            cur: Res | None = Res("mod", ())
        elif first == "self":
            cur = Res("mod", mod)
        elif first == "super":
            cur = Res("mod", mod[:-1])
            while rest and rest[0] == "super":
                cur = Res("mod", cur.mod[:-1])
                rest = rest[1:]
        else:
            cur = self.name_in(mod, first, seen)
        for s in rest:
            if cur is None:
                return None
            if cur.kind == "mod":
                cur = self.name_in(cur.mod, s, seen)
            elif cur.kind == "item" and cur.item is not None:
                cur = Res("variant" if cur.item.kind == "enum" and _has_variant(cur.item, s) else "assoc", item=cur.item, member=s)
            else:
                return None
        return cur

    def name_in(self, mod: ModPath, name: str, seen: set) -> Res | None:
        key = (mod, name)
        if key in seen:
            return None
        seen.add(key)
        info = self.mods.get(mod)
        if info is None:
            return None
        if name in info.items:
            return Res("item", item=info.items[name][0])
        if name in info.children:
            return Res("mod", info.children[name])
        if name in info.uses:
            return self.resolve(mod, info.uses[name], seen)
        for g in info.globs:
            tgt = self.resolve(mod, g, seen)
            if tgt is None:
                continue
            if tgt.kind == "mod":
                hit = self.name_in(tgt.mod, name, seen)
                if hit is not None:
                    return hit
            elif tgt.kind == "item" and tgt.item is not None and tgt.item.kind == "enum" and _has_variant(tgt.item, name):
                return Res("variant", item=tgt.item, member=name)
        return None


def _has_variant(enum: Item, name: str) -> bool:
    body = enum.node.child_by_field_name("body")
    for v in body.children if body is not None else []:
        if v.type == "enum_variant" and _text(v.child_by_field_name("name")) == name:
            return True
    return False


def _use_tree(text: str, prefix: list[str] | None = None) -> list[tuple[str, list[str]]]:
    """``a::{b, c::D as E, self, g::*}`` -> [(b, a::b), (E, a::c::D), (a, a), (*, a::g)]."""
    prefix = prefix or []
    t = " ".join(text.split()).strip()
    if not t:
        return []
    if t.endswith("}"):
        head, _, body = t.partition("{")
        base = prefix + [s for s in head.strip().rstrip(":").split("::") if s]
        out: list[tuple[str, list[str]]] = []
        for part in _split_top(body[:-1]):
            out += _use_tree(part, base)
        return out
    alias = None
    if " as " in t:
        t, alias = (x.strip() for x in t.split(" as ", 1))
    segs = [s.strip() for s in t.split("::") if s.strip()]
    if not segs:
        return []
    if segs[-1] == "*":
        return [("*", prefix + segs[:-1])]
    if segs[-1] == "self":
        segs = segs[:-1]
        full = prefix + segs
        return [(alias or full[-1], full)] if full else []
    full = prefix + segs
    if alias == "_":
        return []
    return [(alias or full[-1], full)]


def _split_top(text: str) -> list[str]:
    parts, depth, cur = [], 0, ""
    for ch in text:
        if ch == "{":
            depth += 1
        elif ch == "}":
            depth -= 1
        if ch == "," and depth == 0:
            parts.append(cur)
            cur = ""
            continue
        cur += ch
    parts.append(cur)
    return [p for p in parts if p.strip()]


_CACHE: dict[str, tuple[tuple, Crate]] = {}


def crate_for(file: str, source: str | None = None) -> Crate:
    """The crate ``file`` belongs to (``source`` overrides its contents)."""
    file = os.path.normpath(os.path.abspath(file))
    root = _root_for(file)
    given = {file: source} if source is not None else {}
    if root != file:
        stamp = _stamp(root, given)
        hit = _CACHE.get(root)
        if hit is not None and hit[0] == stamp:
            crate = hit[1]
        else:
            crate = Crate(root, given)
            _CACHE[root] = (_stamp(root, given, crate), crate)
        if file in crate.sources:
            return crate
    return Crate(file, given)


def _root_for(file: str) -> str:
    d = os.path.dirname(file)
    while True:
        if os.path.exists(os.path.join(d, "Cargo.toml")):
            for cand in ("src/lib.rs", "src/main.rs"):
                p = os.path.normpath(os.path.join(d, cand))
                if os.path.exists(p):
                    return p
            return file
        up = os.path.dirname(d)
        if up == d:
            return file
        d = up


def _stamp(root: str, given: dict[str, str], crate: Crate | None = None) -> tuple:
    hit = _CACHE.get(root)
    files = sorted((crate or (hit[1] if hit else None)).sources) if (crate or hit) else [root]  # type: ignore[union-attr]
    out = []
    for f in files:
        if f in given:
            out.append((f, hash(given[f])))
            continue
        try:
            out.append((f, os.stat(f).st_mtime_ns))
        except OSError:
            out.append((f, None))
    return tuple(out)
