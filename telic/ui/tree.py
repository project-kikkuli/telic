"""The app as a user perceives it: an accessibility tree, on any platform.

A driver turns whatever the platform exposes (the browser's accessibility
tree, UIAutomator, XCUITest) into ``Node``s. Everything above the driver
(abstraction, learning, checking) sees only roles, names and states.
"""

from __future__ import annotations

import json
import re
from dataclasses import dataclass, field

INTERACTIVE = {
    "button", "link", "checkbox", "switch", "radio", "tab", "menuitem", "menuitemcheckbox", "menuitemradio",
    "option", "combobox", "textbox", "searchbox", "slider", "spinbutton", "treeitem",
}
OVERLAYS = {"dialog", "alertdialog", "menu"}
ITEMS = {"listitem", "row", "article", "treeitem"}
TEXT_ENTRY = {"textbox", "searchbox"}
STATE_WORDS = ("checked", "mixed", "disabled", "expanded", "selected", "pressed")


@dataclass
class Node:
    role: str
    name: str = ""
    value: str | None = None
    states: frozenset[str] = frozenset()
    ref: str | None = None  # the driver's handle, valid for the snapshot it came from
    url: str | None = None
    pointer: bool = False  # a generic element the pointer can click (no role, but a click handler)
    children: list["Node"] = field(default_factory=list)

    def walk(self):
        yield self
        for c in self.children:
            yield from c.walk()

    def text(self) -> str:
        """Visible text of the subtree, for naming a clickable element without a role."""
        parts = [self.name] if self.name else []
        if self.value and self.role not in INTERACTIVE:
            parts.append(self.value)
        for c in self.children:
            t = c.text()
            if t:
                parts.append(t)
        return " ".join(" ".join(parts).split())

    @property
    def label(self) -> str:
        return f"{self.role} {json.dumps(self.name, ensure_ascii=False)}" if self.name else self.role


@dataclass
class Snapshot:
    screen: str  # route or screen name
    root: Node

    def nodes(self):
        return self.root.walk()

    def overlays(self) -> list[str]:
        return sorted(n.label for n in self.nodes() if n.role in OVERLAYS)


@dataclass(frozen=True)
class Action:
    kind: str  # click | fill | key | select | press
    sig: str  # identity across states: 'button "Close"', 'key Escape', 'listitem › button 2'
    label: str  # what a person reads in a trace: 'click button "Close"'
    ref: str | None = None
    arg: str | None = None


def _q(s: str) -> str:
    return json.dumps(s, ensure_ascii=False)


def actions(snap: Snapshot, *, text: str = "telic", keys: tuple[str, ...] = (), ignore: tuple[str, ...] = (), leaves=None) -> tuple[list[Action], dict[str, int]]:
    """What a user can do in this state, and the repeated item groups seen
    (``list "Notes" › listitem`` -> how many). Only the first item of a group
    is acted on: the rest behave alike, and acting on each would make every
    list length a new state."""
    out: list[Action] = []
    groups: dict[str, int] = {}

    def add(n: Node, sig: str, where: str) -> None:
        name = f" {_q(n.name)}" if n.name else ""
        what = f"{n.role}{name}"
        if any(re.search(p, what) or re.search(p, sig) for p in ignore):
            return
        if n.role in TEXT_ENTRY or (n.role == "combobox" and not any(c.role == "option" for c in n.children)):
            out.append(Action("fill", "fill " + sig, f"type {_q(text)} into {what}{where}", n.ref, text))
        elif n.role == "combobox":
            for o in n.children:
                if o.role == "option" and "selected" not in o.states and "disabled" not in o.states:
                    out.append(Action("select", f"select {sig} = {_q(o.name)}", f"choose {_q(o.name)} in {what}{where}", n.ref, o.name))
        elif n.role in ("slider", "spinbutton"):
            out.append(Action("press", f"increase {sig}", f"increase {what}{where}", n.ref, "ArrowRight" if n.role == "slider" else "ArrowUp"))
        else:
            out.append(Action("click", sig, f"click {what}{where}", n.ref))

    def visit(n: Node, item: str | None, first: bool, pos: dict[str, int], seen: dict[str, int]) -> None:
        interactive = (n.role in INTERACTIVE or n.pointer) and n.ref is not None and n.role != "option"
        if interactive and "disabled" not in n.states and not (n.url is not None and leaves is not None and leaves(n)):
            role = n.role if not n.pointer or n.role in INTERACTIVE else "clickable"
            shown = n if role != "clickable" else Node("clickable", n.text()[:60], ref=n.ref)
            if item is not None:
                pos[role] = pos.get(role, 0) + 1
                sig = f"{item} › {role} {pos[role]}"
                if first:
                    add(shown, sig, " in the first " + item.split(" › ")[-1])
            else:
                sig = f"{role} {_q(shown.name)}" if shown.name else role
                seen[sig] = seen.get(sig, 0) + 1
                if seen[sig] > 1:
                    sig += f" #{seen[sig]}"
                add(shown, sig, "")
            return  # what is inside a control is part of the control
        if n.role == "option" and n.ref is not None and item is None and "disabled" not in n.states:
            sig = f"option {_q(n.name)}"
            add(n, sig, "")
            return
        kinds: dict[str, int] = {}
        for c in n.children:
            if c.role in ITEMS and item is None:
                gsig = f"{n.label} › {c.role}"
                k = kinds.get(c.role, 0)
                kinds[c.role] = k + 1
                groups[gsig] = kinds[c.role]
                visit(c, gsig, k == 0, {}, seen)
            else:
                visit(c, item, first, pos, seen)

    visit(snap.root, None, True, {}, {})
    for k in keys:
        out.append(Action("key", f"key {k}", f"press {k}", None, k))
    return out, groups


def controls(snap: Snapshot) -> list[str]:
    """Interactive elements outside repeated items, with their states: which
    buttons are enabled and which boxes are checked is part of the state."""
    out: list[str] = []

    def visit(n: Node, in_item: bool) -> None:
        if n.role in INTERACTIVE and not in_item and n.role != "option":
            st = "".join(f"[{s}]" for s in STATE_WORDS if s in n.states)
            out.append(n.label + st)
            if n.role != "combobox":
                return
        for c in n.children:
            visit(c, in_item or c.role in ITEMS)

    visit(snap.root, False)
    return sorted(out)


def bucket(n: int) -> str:
    return "1" if n == 1 else "2+"


def value_of(n: Node) -> str | None:
    """The user-visible value of a control."""
    if n.role in ("checkbox", "switch", "radio", "menuitemcheckbox", "menuitemradio"):
        return "mixed" if "mixed" in n.states else "checked" if "checked" in n.states else "unchecked"
    if n.role == "button" and ("pressed" in n.states or n.value is None):
        return "pressed" if "pressed" in n.states else "not pressed"
    if n.role == "combobox":
        sel = [c.name for c in n.children if c.role == "option" and "selected" in c.states]
        if sel:
            return sel[0]
    return n.value or ""


# ---------------------------------------------------------------------------
# Screen names from URLs

_ID_SEG = re.compile(r"^(\d+|[0-9a-f]{8,}|[0-9a-f]{8}-[0-9a-f-]{27,}|[A-Za-z0-9_-]{16,})$", re.I)


def route(path: str) -> str:
    """``/notes/42`` -> ``/notes/:id``: a record's id is data, not a screen."""
    segs = path.split("/")
    return "/".join(":id" if s and _ID_SEG.match(s) and any(ch.isdigit() for ch in s) else s for s in segs)
