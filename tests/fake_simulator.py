"""A simulator in a dict: the fixture app's screens as AXe would describe
them, taps by coordinate, and simctl's install/launch/terminate. It stands in
for ``telic.ui.sim`` so the iOS adapter runs without Xcode."""

from __future__ import annotations

import json

W, H = 390, 844
TOP = 59  # below the status bar


def el(
    kind: str,
    label: str = "",
    frame=(0, 0, 0, 0),
    value=None,
    children=(),
    enabled=True,
) -> dict:
    x, y, w, h = frame
    return {
        "type": kind,
        "role": f"AX{kind}",
        "AXLabel": label or None,
        "AXValue": value,
        "AXUniqueId": None,
        "enabled": enabled,
        "frame": {"x": x, "y": y, "width": w, "height": h},
        "children": list(children),
    }


class FakeSimulator:
    def __init__(self, bundle: str = "dev.telic.fixture"):
        self.bundle = bundle
        self.installed = False
        self.running = False
        self.saved: dict[str, bool] = {}  # UserDefaults: survives relaunch, not reinstall
        self.bugs: set[str] = set()
        self.calls: list[tuple[str, ...]] = []
        self._fresh()

    def _fresh(self) -> None:
        self.stack: list[str] = ["Home"]
        self.sheet: str | None = None
        self.unsaved = False
        self.cookies = False
        self.safari = False

    # -- simctl ---------------------------------------------------------------

    def simctl(self, *args: str, timeout: float = 120, check: bool = True) -> str:
        self.calls.append(args)
        cmd = args[0]
        if cmd == "install":
            self.installed = True
        elif cmd == "uninstall":
            self.installed = self.running = False
            self.saved = {}
        elif cmd == "terminate":
            self.running = False
        elif cmd == "launch":
            assert self.installed, "launched before install"
            argv = list(args[3:])
            self.bugs = set(argv[argv.index("-TelicBugs") + 1].split(",")) if "-TelicBugs" in argv else set()
            self.running = True
            self._fresh()
            self.cookies = "banner" in self.bugs
        return ""

    # -- AXe ------------------------------------------------------------------

    def axe(self, *args: str, udid: str, timeout: float = 30) -> str:
        self.calls.append(args)
        cmd = args[0]
        if cmd == "describe-ui":
            if "--point" in args:
                x, y = (float(v) for v in args[args.index("--point") + 1].split(","))
                hit = self._at(x, y)
                return json.dumps([hit] if hit else [])
            return json.dumps(self.tree())
        if cmd == "tap":
            x, y = float(args[args.index("-x") + 1]), float(args[args.index("-y") + 1])
            hit = self._at(x, y)
            if hit is not None:
                self._press(hit["AXLabel"] or "")
            return ""
        return ""

    def _at(self, x: float, y: float) -> dict | None:
        """The topmost leaf under the point: later in the tree is on top."""
        found = None

        def walk(d: dict) -> None:
            nonlocal found
            f = d["frame"]
            if not d["children"] and f["x"] <= x < f["x"] + f["width"] and f["y"] <= y < f["y"] + f["height"]:
                found = d
            for c in d["children"]:
                walk(c)

        for r in self.tree():
            walk(r)
        return found

    def _press(self, label: str) -> None:
        top = self.stack[-1]
        if self.safari:
            return
        if self.cookies and label == "Accept":
            self.cookies = False
        elif self.sheet == "Help" and label == "Close" or self.sheet == "Menu" and label in ("Refresh", "Cancel"):
            self.sheet = None
        elif self.sheet is None and top == "Home" and label in ("Settings", "About"):
            self.stack.append(label)
        elif self.sheet is None and top == "Home" and label in ("Help", "Menu"):
            self.sheet = label
        elif self.sheet is None and top != "Home" and label == "Home":
            self.stack.pop()
        elif self.sheet is None and top == "Settings" and label == "Dark mode":
            if "forget" in self.bugs:
                self.unsaved = not self.unsaved
            else:
                self.saved["dark"] = not self.saved.get("dark", False)
        elif self.sheet is None and top == "About" and label == "Website":
            self.safari = True

    def tree(self) -> list[dict]:
        if not self.running:
            return [
                el(
                    "Application",
                    "Home screen",
                    (0, 0, W, H),
                    children=[el("Button", "Fixture", (20, 100, 60, 60))],
                )
            ]
        if self.safari:
            return [
                el(
                    "Application",
                    "Safari",
                    (0, 0, W, H),
                    children=[el("TextField", "Address", (20, TOP, 350, 40))],
                )
            ]
        kids: list[dict] = []
        if self.sheet == "Help":
            # a presented sheet hides what is under it from accessibility
            body = [
                el("Heading", "Help", (0, TOP + 40, W, 44)),
                el("StaticText", "Write notes.", (16, 200, 200, 20)),
            ]
            if "trap" not in self.bugs:
                body.append(el("Button", "Close", (16, TOP + 40, 60, 44)))
            kids.append(el("Sheet", "Help", (0, TOP + 20, W, H - TOP - 20), children=body))
        elif self.sheet == "Menu":
            kids.append(
                el(
                    "Sheet",
                    "Menu",
                    (8, 600, W - 16, 236),
                    children=[
                        el("StaticText", "Menu", (8, 600, W - 16, 40)),
                        el("Button", "Refresh", (8, 640, W - 16, 56)),
                        el("Button", "Cancel", (8, 760, W - 16, 56)),
                    ],
                )
            )
        else:
            top = self.stack[-1]
            bar = [el("Heading", top, (16, TOP + 44, 200, 40))]
            if top == "Home":
                bar.append(el("Button", "Menu", (320, TOP, 60, 44)))
            else:
                bar.insert(0, el("Button", "Home", (8, TOP, 80, 44)))
            kids.append(el("NavigationBar", top, (0, TOP, W, 96), children=bar))
            if top == "Home":
                kids += [el("Button", n, (0, 200 + 44 * i, W, 44)) for i, n in enumerate(("Settings", "About", "Help"))]
            elif top == "Settings":
                on = self.unsaved if "forget" in self.bugs else self.saved.get("dark", False)
                kids.append(el("Switch", "Dark mode", (0, 200, W, 44), value="1" if on else "0"))
            elif top == "About":
                kids += [
                    el("StaticText", "A fixture for telic.", (16, 200, 300, 20)),
                    el("Link", "Website", (16, 240, 100, 20)),
                ]
            if self.cookies:
                kids.append(
                    el(
                        "Other",
                        "",
                        (0, TOP, W, 52),
                        children=[
                            el("StaticText", "We use cookies", (16, TOP, 200, 52)),
                            el("Button", "Accept", (300, TOP, 90, 52)),
                        ],
                    )
                )
        return [el("Application", "Fixture", (0, 0, W, H), children=kids)]
