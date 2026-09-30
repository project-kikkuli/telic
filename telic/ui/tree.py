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
LANDMARKS = {"banner", "complementary", "contentinfo", "form", "main", "navigation", "region", "search"}
TEXT_ENTRY = {"textbox", "searchbox"}
LIVE = {"status", "alert", "log", "marquee", "timer"}  # announcements: transient, not part of the state
# What a person would type into a field, by its name (checked before the fallback text).
FILL = (
    (r"e-?mail", "telic@example.com"),
    (r"pass(word|phrase|code)?\b|\bpin\b", "Telic-pass-123"),
    (r"phone|mobile|\btel\b", "5550100"),
    (r"\burl\b|website|homepage", "https://example.com"),
    (r"\bdate\b|\bdue\b|birthday|deadline", "2030-01-15"),
    (r"\btime\b", "09:30"),
    (r"\bzip\b|postal", "94103"),
    (r"amount|price|\bqty\b|quantity|\bnumber\b|\bage\b|\bcount\b", "3"),
)


def fill_value(name: str, overrides: tuple[tuple[str, str], ...] = (), default: str = "telic") -> str:
    for pat, v in tuple(overrides) + FILL:
        if re.search(pat, name, re.I):
            return v
    return default
STATE_WORDS = ("checked", "mixed", "disabled", "expanded", "selected", "pressed")
# States that change what the user can do next. Which box is checked or which
# option is chosen is data (like typed text): a lemma that cares names it.
STRUCTURAL = ("disabled", "expanded", "pressed")


@dataclass
class Node:
    role: str
    name: str = ""
    value: str | None = None
    states: frozenset[str] = frozenset()
    ref: str | None = None  # the driver's handle, valid for the snapshot it came from
    url: str | None = None
    pointer: bool = False  # a generic element the pointer can click (no role, but a click handler)
    form: str | None = None  # for a text field in a form: the form's submit control ("" if Enter submits)
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


def _data(name: str) -> str:
    """A name with its numbers blanked: 'All tasks 5' and 'All tasks 6' are one control."""
    return re.sub(r"\d+", "#", name)


def actions(
    snap: Snapshot, *, text: str = "telic", fill: tuple[tuple[str, str], ...] = (), keys: tuple[str, ...] = (), ignore: tuple[str, ...] = (), leaves=None
) -> tuple[list[Action], dict[str, int]]:
    """What a user can do in this state, and the repeated item groups seen
    (``list "Notes" › listitem`` -> how many). Only the first item of a group
    is acted on: the rest behave alike, and acting on each would make every
    list length a new state."""
    out: list[Action] = []
    groups: dict[str, int] = {}
    containers: dict[str, int] = {}  # two unnamed lists are 'list' and 'list #2'

    def add(n: Node, sig: str, where: str) -> None:
        name = f" {_q(n.name)}" if n.name else ""
        what = f"{n.role}{name}"
        if any(re.search(p, what) or re.search(p, sig) for p in ignore):
            return
        if n.role in TEXT_ENTRY or (n.role == "combobox" and not any(c.role == "option" for c in n.children)):
            v = fill_value(n.name, fill, text)
            out.append(Action("fill", "fill " + sig, f"type {_q(v)} into {what}{where}", n.ref, v))
        elif n.role == "combobox":
            for o in n.children:
                if o.role == "option" and "disabled" not in o.states:
                    out.append(Action("select", f"select {sig} = {_q(o.name)}", f"choose {_q(o.name)} in {what}{where}", n.ref, o.name))
        elif n.role in ("slider", "spinbutton"):
            out.append(Action("press", f"increase {sig}", f"increase {what}{where}", n.ref, "ArrowRight" if n.role == "slider" else "ArrowUp"))
        else:
            out.append(Action("click", sig, f"click {what}{where}", n.ref))

    def visit(n: Node, item: str | None, first: bool, pos: dict[str, int], seen: dict[str, int]) -> None:
        if n.role in LIVE:
            return
        interactive = (n.role in INTERACTIVE or n.pointer) and n.ref is not None and n.role != "option"
        if interactive and n.role in TEXT_ENTRY and n.form is not None:
            return
        if interactive and "disabled" not in n.states and not (n.url is not None and leaves is not None and leaves(n)):
            role = n.role if not n.pointer or n.role in INTERACTIVE else "clickable"
            shown = n if role != "clickable" else Node("clickable", n.text()[:60], ref=n.ref)
            if item is not None:
                pos[role] = pos.get(role, 0) + 1
                sig = f"{item} › {role} {pos[role]}"
                if first:
                    add(shown, sig, " in the first " + item.split(" › ")[-1])
            else:
                sig = f"{role} {_q(_data(shown.name))}" if shown.name else role
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
        here = ""
        for c in n.children:
            if c.role in ITEMS and item is None:
                if not here:
                    base = f"{n.role} {_q(_data(n.name))}" if n.name else n.role
                    containers[base] = containers.get(base, 0) + 1
                    here = base + (f" #{containers[base]}" if containers[base] > 1 else "")
                gsig = f"{here} › {c.role}"
                k = kinds.get(c.role, 0)
                kinds[c.role] = k + 1
                groups[gsig] = kinds[c.role]
                visit(c, gsig, k == 0, {}, seen)
            else:
                visit(c, item, first, pos, seen)

    forms: dict[str, list[Node]] = {}

    def visit_fields(n: Node, item: bool) -> None:
        for c in n.children:
            if c.role in LIVE:
                continue
            if c.role in TEXT_ENTRY and c.form is not None and c.ref is not None and "disabled" not in c.states and not item:
                forms.setdefault(c.form, []).append(c)
            visit_fields(c, item or c.role in ITEMS)

    visit_fields(snap.root, False)
    visit(snap.root, None, True, {}, {})
    # A form is filled in and sent as one action: what was typed is data, and
    # half-filled forms would multiply the states for nothing.
    for submit, fields in forms.items():
        names = [f.name or f.role for f in fields]
        if any(re.search(p, "form " + submit) for p in ignore):
            continue
        button = next((n for n in snap.nodes() if n.role == "button" and n.name == submit and n.ref is not None), None) if submit else None
        values = [[f.ref, fill_value(f.name, fill, text)] for f in fields]
        how = f"click button {_q(submit)}" if button is not None else "press Enter"
        out.append(Action("form", f"submit form {_q(submit or names[-1])}", f"fill in {', '.join(names)} and {how}", button.ref if button is not None else None, json.dumps(values)))
    for k in keys:
        out.append(Action("key", f"key {k}", f"press {k}", None, k))
    return out, groups


def controls(snap: Snapshot) -> list[str]:
    """Interactive elements outside repeated items, with their states: which
    buttons are enabled and which boxes are checked is part of the state."""
    out: list[str] = []

    def visit(n: Node, in_item: bool) -> None:
        if n.role in LIVE:
            return
        if n.role in INTERACTIVE and not in_item and n.role != "option":
            st = "".join(f"[{s}]" for s in STRUCTURAL if s in n.states)
            if n.role in TEXT_ENTRY and n.value and n.form is None:
                st += "[filled]"  # what was typed is data, whether anything was is state
            out.append(f"{n.role} {_q(_data(n.name))}{st}" if n.name else n.role + st)
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
