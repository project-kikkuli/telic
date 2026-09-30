"""What the app's source says that its accessibility tree does not: the keys
its handlers listen for (so they are pressed like any other action), and the
variables its handlers change that decide what renders (so the model reads
them, or no verdict that needs them is "proved")."""

from __future__ import annotations

import json
import os
import re
import subprocess
from dataclasses import dataclass, field
from pathlib import Path

from .spec import SKIP_DIRS

WEB_EXT = (".ts", ".tsx", ".mts", ".cts", ".js", ".jsx", ".mjs", ".cjs", ".svelte", ".vue")


@dataclass(frozen=True)
class Key:
    key: str  # as the driver presses it: 'Escape', 'ControlOrMeta+s'
    path: str
    line: int

    def at(self) -> str:
        return f"{self.path}:{self.line}"


@dataclass(frozen=True)
class Hidden:
    """A variable a handler changes that decides what renders."""

    name: str
    path: str
    line: int
    writes: tuple[int, ...] = ()
    reads: tuple[int, ...] = ()
    clock: tuple[int, ...] = ()  # also written by a timer
    component: str | None = None
    react: bool = False
    unique: bool = True  # the only binding of that name in its file
    kind: str = "var"  # or "storage": what the page keeps in localStorage, sessionStorage, cookies or IndexedDB (``name``)
    # what it can change in the tree: "structure" (which elements exist, their roles,
    # whether they can be used) and "content" (what the tree shows of them: names, states, values)
    affects: tuple[str, ...] = ("structure", "content")

    def at(self) -> str:
        return f"{self.path}:{self.line}"

    def describe(self) -> str:
        w = f", set at line {', '.join(map(str, self.writes))}" if self.writes else ""
        return f"`{self.name}` ({self.at()}{w})"


@dataclass(frozen=True)
class Gap:
    """A key handler whose keys the source does not spell out."""

    path: str
    line: int
    why: str

    def describe(self) -> str:
        return f"{self.path}:{self.line} ({self.why})"


@dataclass
class Facts:
    keys: list[Key] = field(default_factory=list)
    hidden: list[Hidden] = field(default_factory=list)
    gaps: list[Gap] = field(default_factory=list)
    errors: list[str] = field(default_factory=list)


def _files(top: str, ext: tuple[str, ...]) -> list[str]:
    out = []
    for dirpath, dirnames, filenames in os.walk(top):
        dirnames[:] = sorted(d for d in dirnames if d not in SKIP_DIRS and not d.startswith("."))
        for f in sorted(filenames):
            if f.endswith(ext) and not f.endswith((".d.ts", ".config.js", ".config.ts", ".config.mjs", ".spec.ts", ".test.ts", ".test.tsx", ".spec.tsx")):
                out.append(os.path.join(dirpath, f))
    return out


def scan(top: str, platform: str = "web") -> Facts:
    """Keys and hidden state in the app under ``top``."""
    facts = Facts()
    if platform == "ios":
        for f in _files(top, (".swift",)):
            try:
                text = Path(f).read_text(encoding="utf-8")
            except (OSError, UnicodeDecodeError):
                continue
            facts.keys += swift_keys(text, os.path.relpath(f, top))
    else:
        _web(top, facts)
    seen: set[str] = set()
    facts.keys = [k for k in facts.keys if not (k.key in seen or seen.add(k.key))]
    return facts


def _web(top: str, facts: Facts) -> None:
    from ..frontend import typescript

    files = []
    for f in _files(top, WEB_EXT):
        try:
            files.append({"path": os.path.relpath(f, top), "text": Path(f).read_text(encoding="utf-8")})
        except (OSError, UnicodeDecodeError):
            continue
    if not files:
        return
    try:
        typescript.ensure_installed()
        p = subprocess.run(
            [typescript._node(), str(typescript.HERE / "uiscan.mjs")], input=json.dumps({"files": files}), capture_output=True, text=True, timeout=120, check=False
        )
        got = json.loads(p.stdout)
    except (typescript.FrontendUnavailable, subprocess.SubprocessError, OSError, ValueError) as e:
        facts.errors.append(f"reading the app's source: {e}")
        return
    facts.errors += got.get("errors", [])
    facts.keys += [Key(k["key"], k["path"], k["line"]) for k in got.get("keys", [])]
    facts.hidden += [
        Hidden(
            s["name"],
            s["path"],
            s["line"],
            tuple(s.get("writes", ())),
            tuple(s.get("reads", ())),
            tuple(s.get("clock", ())),
            s.get("component"),
            bool(s.get("react")),
            bool(s.get("unique", True)),
            affects=tuple(s.get("affects", ("structure", "content"))),
        )
        for s in got.get("state", [])
    ]
    first: dict[str, list[dict]] = {}
    for s in got.get("storage", []):
        first.setdefault(s["api"], []).append(s)
    for api, uses in sorted(first.items()):
        writes = tuple(sorted({u["line"] for u in uses if u["write"] and u["path"] == uses[0]["path"]}))[:3]
        facts.hidden.append(Hidden(api, uses[0]["path"], uses[0]["line"], writes, kind="storage"))
    facts.gaps = [Gap(g["path"], g["line"], g["why"]) for g in got.get("unresolved", [])]


# ---------------------------------------------------------------------------
# SwiftUI and UIKit key commands

_SWIFT_MODS = {"command": "Meta", "shift": "Shift", "option": "Alt", "control": "Control", "alternate": "Alt"}
_SWIFT_KEYS = {
    "escape": "Escape", "cancelAction": "Escape", "defaultAction": "Enter", "return": "Enter", "space": "Space", "tab": "Tab",
    "delete": "Backspace", "deleteForward": "Delete", "upArrow": "ArrowUp", "downArrow": "ArrowDown", "leftArrow": "ArrowLeft",
    "rightArrow": "ArrowRight", "home": "Home", "end": "End", "pageUp": "PageUp", "pageDown": "PageDown",
    "inputEscape": "Escape", "inputUpArrow": "ArrowUp", "inputDownArrow": "ArrowDown", "inputLeftArrow": "ArrowLeft", "inputRightArrow": "ArrowRight",
}
# KeyboardShortcut values that carry their own (empty) modifiers
_SHORTCUTS = {"cancelAction", "defaultAction"}
_SHORTCUT = re.compile(r"\.keyboardShortcut\(\s*(?:\"(?P<ch>[^\"\\]|\\.)\"|\.(?P<name>\w+))\s*(?:,\s*modifiers:\s*(?P<mods>\[[^\]]*\]|\.\w+))?")
_KEYPRESS = re.compile(r"\.onKeyPress\(\s*(?:keys:\s*\[\s*)?(?:\"(?P<ch>[^\"\\])\"|\.(?P<name>\w+))")
_UIKEY = re.compile(r"UIKeyCommand\(\s*(?:title:[^,]*,\s*(?:image:[^,]*,\s*)?action:[^,]*,\s*)?input:\s*(?:\"(?P<ch>[^\"\\])\"|UIKeyCommand\.(?P<name>\w+))\s*,\s*modifierFlags:\s*(?P<mods>\[[^\]]*\]|\.\w+)")
_EXIT = re.compile(r"\.onExitCommand\b")


def _mods(text: str | None, default: tuple[str, ...]) -> list[str]:
    if text is None:
        return list(default)
    return sorted({_SWIFT_MODS[m] for m in re.findall(r"\.(\w+)", text) if m in _SWIFT_MODS})


def swift_keys(text: str, path: str) -> list[Key]:
    out: list[Key] = []

    def line(i: int) -> int:
        return text.count("\n", 0, i) + 1

    def add(ch: str | None, name: str | None, mods: list[str], at: int) -> None:
        key = ch.lower() if ch else _SWIFT_KEYS.get(name or "")
        if key:
            out.append(Key("+".join([*mods, key]), path, line(at)))

    for m in _SHORTCUT.finditer(text):
        name = m.group("name")
        mods = [] if name in _SHORTCUTS else _mods(m.group("mods"), ("Meta",))
        add(m.group("ch"), name, mods, m.start())
    for m in _KEYPRESS.finditer(text):
        add(m.group("ch"), m.group("name"), [], m.start())
    for m in _UIKEY.finditer(text):
        add(m.group("ch"), m.group("name"), _mods(m.group("mods"), ()), m.start())
    for m in _EXIT.finditer(text):
        out.append(Key("Escape", path, line(m.start())))
    return out
