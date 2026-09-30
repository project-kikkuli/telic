"""The iOS adapter: an app in the iOS Simulator, read through its
accessibility tree and touched where a finger would touch it (AXe)."""

from __future__ import annotations

import json
import time
from typing import Any

from . import sim
from .driver import Driver, DriverError
from .tree import Action, Node, Snapshot

# AX element types (AXe's ``type``, else ``role`` without "AX") -> telic roles
ROLES = {
    "Button": "button",
    "Link": "link",
    "StaticText": "text",
    "Heading": "heading",
    "TextField": "textbox",
    "SecureTextField": "textbox",
    "TextView": "textbox",
    "TextArea": "textbox",
    "SearchField": "searchbox",
    "Switch": "switch",
    "Toggle": "switch",
    "CheckBox": "switch",
    "Slider": "slider",
    "Stepper": "spinbutton",
    "Incrementor": "spinbutton",
    "Tab": "tab",
    "RadioButton": "tab",
    "TabBar": "tablist",
    "TabGroup": "tablist",
    "Table": "list",
    "CollectionView": "list",
    "List": "list",
    "Cell": "listitem",
    "Image": "img",
    "Alert": "alertdialog",
    "Sheet": "dialog",
    "Dialog": "dialog",
    "Popover": "dialog",
    "Menu": "menu",
    "MenuItem": "menuitem",
    "PopUpButton": "button",
    "MenuButton": "button",
    "SegmentedControl": "tablist",
    "NavigationBar": "banner",
    "Toolbar": "toolbar",
    "ProgressIndicator": "progressbar",
}
# Keyboard keys by the names [ui] keys uses, as HID usage codes
KEYS = {
    "Enter": 40,
    "Return": 40,
    "Escape": 41,
    "Backspace": 42,
    "Tab": 43,
    "Space": 44,
    "ArrowRight": 79,
    "ArrowLeft": 80,
    "ArrowDown": 81,
    "ArrowUp": 82,
}


def _kind(d: dict[str, Any]) -> str:
    t = d.get("type") or ""
    if t:
        return str(t)
    r = str(d.get("role") or "")
    return r.removeprefix("AX")


def _frame(d: dict[str, Any]) -> tuple[float, float, float, float] | None:
    f = d.get("frame")
    if not isinstance(f, dict):
        return None
    try:
        return float(f["x"]), float(f["y"]), float(f["width"]), float(f["height"])
    except (KeyError, TypeError, ValueError):
        return None


def _on(v: Any) -> bool:
    return str(v).strip().lower() in ("1", "true", "on", "yes")


def parse_ax(
    roots: list[dict[str, Any]],
    frames: dict[str, tuple[float, float, float, float]] | None = None,
) -> Node:
    """AXe's ``describe-ui`` JSON -> a Node tree. ``frames`` collects each
    node's frame by ref, for touching and hit-testing it."""
    frames = {} if frames is None else frames
    root = Node("root")

    def visit(d: dict[str, Any], parent: Node, path: str) -> None:
        kind = _kind(d)
        role = ROLES.get(kind, "generic")
        label = " ".join(str(d.get("AXLabel") or d.get("title") or "").split())
        value = d.get("AXValue")
        n = Node(role, label, ref=path)
        states: set[str] = set()
        if d.get("enabled") is False:
            states.add("disabled")
        if role == "switch":
            if _on(value):
                states.add("checked")
        elif value not in (None, ""):
            n.value = str(value)
        if role == "text":
            n.value, n.name = n.name, ""
        if role == "tab" and _on(value):
            states.add("selected")
        n.states = frozenset(states)
        f = _frame(d)
        if f is not None:
            frames[path] = f
        parent.children.append(n)
        for i, c in enumerate(d.get("children") or []):
            visit(c, n, f"{path}.{i}")

    for i, d in enumerate(roots):
        visit(d, root, str(i))
    return root


def _app_label(roots: list[dict[str, Any]]) -> str:
    for d in roots:
        if _kind(d) == "Application":
            return str(d.get("AXLabel") or "")
    return ""


def screen_of(root: Node) -> str:
    """The screen's name: the navigation bar's title (the first heading),
    else ``/``."""
    for n in root.walk():
        if n.role == "banner" and n.name:
            return n.name
    for n in root.walk():
        if n.role == "heading" and n.name:
            return n.name
    return "/"


class IosDriver(Driver):
    name = "ios"

    def __init__(
        self,
        app: str,
        device: str,
        *,
        launch_args: list[str] | None = None,
        settle_ms: int = 50,
        timeout_ms: int = 5000,
    ):
        self.app = app
        self.bundle = sim.bundle_id(app)
        self.device = device
        self.launch_args = list(launch_args or [])
        self.settle_ms = settle_ms
        self.timeout_ms = timeout_ms
        self.udid = ""
        self.mine = False  # this driver booted the simulator, so it shuts it down
        self.raw: list[dict[str, Any]] = []
        self.text = ""
        self.frames: dict[str, tuple[float, float, float, float]] = {}
        self.names: dict[str, str] = {}
        self.label = ""
        self.dialogs = 0

    def start(self) -> None:
        why = sim.available()
        if why:
            raise DriverError(why)
        self.udid = sim.device(self.device)
        self.mine = sim.boot(self.udid)

    def stop(self) -> None:
        if not self.udid:
            return
        sim.simctl("terminate", self.udid, self.bundle, check=False)
        if self.mine:
            sim.simctl("shutdown", self.udid, check=False)

    def viewport(self, width: int, height: int) -> None:
        raise DriverError("on iOS the screen size is the device's: list devices in [ui] devices")

    def reset(self) -> None:
        sim.simctl("terminate", self.udid, self.bundle, check=False)
        sim.simctl("uninstall", self.udid, self.bundle, check=False)
        sim.simctl("install", self.udid, self.app)
        self._launch()

    def reopen(self) -> None:
        sim.simctl("terminate", self.udid, self.bundle, check=False)
        self._launch()

    def _launch(self) -> None:
        sim.simctl("launch", self.udid, self.bundle, *self.launch_args)
        self.label = ""
        self._settle()
        self.label = _app_label(self.raw)

    def _describe(self, *extra: str) -> list[dict[str, Any]]:
        out = sim.axe("describe-ui", *extra, udid=self.udid, timeout=self.timeout_ms / 1000 * 3)
        try:
            got = json.loads(out)
        except ValueError:
            raise DriverError(f"AXe answered something that is not JSON: {out[:120]!r}", moved=True) from None
        return got if isinstance(got, list) else [got]

    def _settle(self) -> None:
        """Until two looks in a row, ``settle_ms`` apart, see the same tree."""
        deadline = time.monotonic() + self.timeout_ms / 1000
        last = None
        while True:
            raw = self._describe()
            text = json.dumps(raw, sort_keys=True)
            if text == last or time.monotonic() > deadline:
                self.raw, self.text = raw, text
                return
            last = text
            time.sleep(self.settle_ms / 1000)

    def screen(self, root: Node) -> str:
        now = _app_label(self.raw)
        if self.label and now and now != self.label:
            return f"outside:{now}"
        return screen_of(root)

    def observe(self) -> Snapshot:
        self.frames = {}
        root = parse_ax(self.raw, self.frames)
        self.names = {n.ref: n.label for n in root.walk() if n.ref is not None}
        return Snapshot(self.screen(root), root)

    def _points(self, ref: str) -> list[tuple[str, float, float]]:
        x, y, w, h = self.frames[ref]
        d = max(1.0, min(3.0, w / 4, h / 4))
        return [
            ("center", x + w / 2, y + h / 2),
            ("top-left corner", x + d, y + d),
            ("top-right corner", x + w - d, y + d),
            ("bottom-left corner", x + d, y + h - d),
            ("bottom-right corner", x + w - d, y + h - d),
        ]

    def _at(self, ref: str, x: float, y: float) -> str | None:
        """What a finger at (x, y) touches instead of this element, or None if it touches it."""
        hit = self._describe("--point", f"{round(x)},{round(y)}")
        if not hit:
            return "nothing (outside the app)"
        top = hit[-1] if isinstance(hit, list) else hit
        f = _frame(top)
        mine = self.frames.get(ref)
        if f is not None and mine is not None and all(abs(a - b) < 1 for a, b in zip(f, mine)):
            return None
        # a touch on a control's label or icon is a touch on the control
        if f is not None and mine is not None and f[0] >= mine[0] - 1 and f[1] >= mine[1] - 1 and f[0] + f[2] <= mine[0] + mine[2] + 1 and f[1] + f[3] <= mine[1] + mine[3] + 1:
            return None
        kind = ROLES.get(_kind(top), _kind(top).lower() or "element")
        label = " ".join(str(top.get("AXLabel") or "").split())
        return f"{kind} {json.dumps(label, ensure_ascii=False)}" if label else kind

    def _screen_size(self) -> tuple[float, float]:
        for d in self.raw:
            f = _frame(d)
            if f is not None and f[2] and f[3]:
                return f[2], f[3]
        return 1e9, 1e9

    def uncovered(self, node: Node) -> tuple[bool, list[tuple[str, str | None]]]:
        ref = node.ref or ""
        if ref not in self.frames:
            return False, []
        *_, w, h = self.frames[ref]
        if w < 2 or h < 2:
            return False, []
        sw, sh = self._screen_size()
        out = []
        for name, px, py in self._points(ref):
            if px < 0 or py < 0 or px >= sw or py >= sh:
                out.append(
                    (
                        f"{name} ({round(px)}, {round(py)})",
                        "the edge of the screen (it is cut off)",
                    )
                )
            else:
                out.append((f"{name} ({round(px)}, {round(py)})", self._at(ref, px, py)))
        return True, out

    def _tap(self, ref: str | None) -> None:
        if ref is None or ref not in self.frames:
            raise DriverError("no element")
        *_, w, h = self.frames[ref]
        if w < 2 or h < 2:
            raise DriverError("not rendered (no size on screen)")
        _, cx, cy = self._points(ref)[0]
        who = self._at(ref, cx, cy)
        if who is not None:
            raise DriverError(f"covered by {who}")
        sim.axe("tap", "-x", str(round(cx)), "-y", str(round(cy)), udid=self.udid)

    def do(self, action: Action) -> None:
        shown = self.text
        if action.kind == "key":
            code = KEYS.get(action.arg or "")
            if code is None:
                raise DriverError(f"no key {action.arg!r} on iOS (known: {', '.join(KEYS)})")
            sim.axe("key", str(code), udid=self.udid)
        elif action.kind == "click":
            self._tap(action.ref)
        elif action.kind == "fill":
            self._tap(action.ref)
            sim.axe("key-combo", "--modifiers", "227", "--key", "4", udid=self.udid)  # select all
            sim.axe("key", "42", udid=self.udid)
            sim.axe("type", action.arg or "", udid=self.udid)
        elif action.kind == "press":
            x, y, w, h = self.frames.get(action.ref or "", (0, 0, 0, 0))
            if action.arg in ("ArrowRight", "ArrowUp"):
                self._tap_at(action.ref, x + w * 0.75 if w > h else x + w / 2, y + h / 2)
            else:
                raise DriverError(f"cannot press {action.arg} on iOS")
        else:
            raise DriverError(f"no {action.kind} on iOS")
        self._settle()
        if self.text == shown:
            time.sleep(0.25)
            self._settle()
        root = parse_ax(self.raw)
        s = self.screen(root)
        if s.startswith("outside:"):
            raise DriverError(f"leaves the app (to {s[8:]})", moved=True)

    def _tap_at(self, ref: str | None, x: float, y: float) -> None:
        who = self._at(ref or "", x, y)
        if who is not None:
            raise DriverError(f"covered by {who}")
        sim.axe("tap", "-x", str(round(x)), "-y", str(round(y)), udid=self.udid)
