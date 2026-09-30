"""The web adapter: a browser (Playwright, Chromium), read through its accessibility tree."""

from __future__ import annotations

import functools
import json
import queue
import re
import threading
import time
from urllib.parse import urljoin, urlsplit

from .driver import Driver, DriverError
from .tree import Action, Node, Snapshot, route

_LINE = re.compile(r"^(?P<indent>\s*)- (?P<body>.*)$")
_ATTR = re.compile(r"\s*\[(?P<a>[^\]]*)\]")
_ROLE = re.compile(r"[a-zA-Z]+")

_HIT_JS = """
(el, block) => {
  el.scrollIntoView({block, inline: 'nearest', behavior: 'instant'});
  const r = el.getBoundingClientRect();
  if (r.width < 2 || r.height < 2) return {rendered: false, points: []};
  const d = Math.max(1, Math.min(3, r.width / 4, r.height / 4));
  const pts = [['center', r.left + r.width / 2, r.top + r.height / 2], ['top-left corner', r.left + d, r.top + d],
               ['top-right corner', r.right - d, r.top + d], ['bottom-left corner', r.left + d, r.bottom - d],
               ['bottom-right corner', r.right - d, r.bottom - d]];
  const labels = [...(el.labels || [])];
  const mine = (h) => h && (h === el || el.contains(h) || labels.some((l) => l.contains(h)) || (h.shadowRoot && h.contains(el)));
  const describe = (h) => {
    if (!h) return 'nothing (outside the page)';
    let s = h.tagName.toLowerCase();
    if (h.id) s += '#' + h.id;
    const cls = (typeof h.className === 'string' ? h.className : '').trim().split(/\\s+/).filter(Boolean).slice(0, 2);
    if (cls.length) s += '.' + cls.join('.');
    const role = h.getAttribute('role');
    if (role) s += ` [role=${role}]`;
    const t = (h.getAttribute('aria-label') || h.innerText || '').trim().replace(/\\s+/g, ' ').slice(0, 40);
    return t ? `${s} "${t}"` : s;
  };
  return {rendered: true, points: pts.map(([n, x, y]) => {
    if (x < 0 || y < 0 || x >= innerWidth || y >= innerHeight) return [n, [Math.round(x), Math.round(y)], 'the edge of the viewport (it is cut off)'];
    const h = document.elementFromPoint(x, y);
    return [n, [Math.round(x), Math.round(y)], mine(h) ? null : describe(h)];
  })};
}
"""

# Installed in every page: when the DOM last changed and how many requests are in flight.
_WATCH_JS = """
(() => {
  if (window.__telic) return;
  const t = window.__telic = {last: performance.now(), pending: 0};
  const bump = () => { t.last = performance.now(); };
  new MutationObserver(bump).observe(document, {subtree: true, childList: true, attributes: true, characterData: true});
  const f = window.fetch;
  if (f) window.fetch = function (...a) { t.pending++; bump(); return f.apply(this, a).finally(() => { t.pending--; bump(); }); };
  const send = XMLHttpRequest.prototype.send;
  XMLHttpRequest.prototype.send = function (...a) { t.pending++; bump(); this.addEventListener('loadend', () => { t.pending--; bump(); }); return send.apply(this, a); };
  addEventListener('hashchange', bump);
  addEventListener('popstate', bump);
})();
"""

# Resolves once nothing has changed for `quiet` ms since the call, no request
# is in flight and no finite animation runs (or after `cap` ms).
_QUIET_JS = """
([quiet, cap]) => new Promise((done) => {
  const start = performance.now();
  const tick = () => {
    const t = window.__telic || {last: start, pending: 0};
    const now = performance.now();
    const moving = document.getAnimations().some((a) => a.playState === 'running' && a.effect && a.effect.getTiming().iterations !== Infinity);
    if ((now - Math.max(t.last, start) >= quiet && !t.pending && !moving) || now - start > cap) return done(now - start);
    setTimeout(tick, 8);
  };
  tick();
})
"""


def parse_aria(text: str) -> Node:
    """Playwright's aria snapshot (YAML-like, with refs) -> a Node tree."""
    root = Node("root")
    stack: list[tuple[int, Node]] = [(-1, root)]
    for raw in text.splitlines():
        m = _LINE.match(raw)
        if not m:
            continue
        indent, body = len(m.group("indent")), m.group("body")
        while stack and stack[-1][0] >= indent:
            stack.pop()
        parent = stack[-1][1]
        if body.startswith("/"):
            key, _, val = body[1:].partition(":")
            val = _unquote(val.strip())
            if key == "url":
                parent.url = val
            elif key == "placeholder" and not parent.name:
                parent.name = val
            continue
        if body.startswith("text:"):
            parent.children.append(Node("text", value=_unquote(body[5:].strip())))
            continue
        rm = _ROLE.match(body)
        if not rm:
            continue
        n = Node(rm.group(0))
        rest = body[rm.end():]
        if rest.startswith(' "'):
            try:
                name, end = json.JSONDecoder().raw_decode(rest, 1)
                n.name = " ".join(str(name).split())
                rest = rest[end:]
            except ValueError:
                pass
        states: set[str] = set()
        while True:
            am = _ATTR.match(rest)
            if not am:
                break
            a = am.group("a")
            rest = rest[am.end():]
            k, _, v = a.partition("=")
            if k == "ref":
                n.ref = v
            elif k == "cursor" and v == "pointer":
                n.pointer = n.role == "generic"
            elif k == "checked" and v == "mixed":
                states.add("mixed")
            elif k in ("checked", "disabled", "expanded", "selected", "pressed") and v in ("", "true"):
                states.add(k)
        n.states = frozenset(states)
        rest = rest.strip()
        if rest.startswith(":"):
            val = rest[1:].strip()
            if val:
                n.value = _unquote(val)
        parent.children.append(n)
        stack.append((indent, n))
    _drop_inherited_pointer(root, False)
    return root


def _drop_inherited_pointer(n: Node, inside: bool) -> None:
    """``cursor: pointer`` is inherited: only the outermost element with it,
    and no control or element inside a control, is its own click target."""
    from .tree import INTERACTIVE

    if n.pointer and (inside or any(c.role in INTERACTIVE for c in n.walk() if c is not n)):
        n.pointer = False
    for c in n.children:
        _drop_inherited_pointer(c, inside or n.pointer or n.role in INTERACTIVE)


def _unquote(v: str) -> str:
    if v.startswith('"'):
        try:
            return str(json.loads(v))
        except ValueError:
            return v.strip('"')
    return v


class _Home:
    """A thread that owns one Playwright instance: its objects may only be
    used from the thread that created them, and workers call from others."""

    def __init__(self):
        self.q: queue.Queue = queue.Queue()
        self.t = threading.Thread(target=self._loop, daemon=True)
        self.t.start()

    def _loop(self) -> None:
        while True:
            item = self.q.get()
            if item is None:
                return
            fn, args, box, done = item
            try:
                box.append((True, fn(*args)))
            except BaseException as e:  # noqa: BLE001 - handed to the caller
                box.append((False, e))
            done.set()

    def call(self, fn, *args):
        if threading.current_thread() is self.t:
            return fn(*args)
        box: list = []
        done = threading.Event()
        self.q.put((fn, args, box, done))
        done.wait()
        ok, v = box[0]
        if ok:
            return v
        raise v

    def close(self) -> None:
        self.q.put(None)


def _confined(fn):
    @functools.wraps(fn)
    def wrap(self, *args):
        return self._home.call(fn, self, *args)

    return wrap


class WebDriver(Driver):
    name = "web"

    def __init__(self, url: str, *, settle_ms: int = 50, timeout_ms: int = 3000, headless: bool = True):
        self.url = url
        self.origin = "{0.scheme}://{0.netloc}".format(urlsplit(url))
        self.settle_ms = settle_ms
        self.timeout_ms = timeout_ms
        self.headless = headless
        self.size = (1280, 800)
        self._pw = self._browser = self._ctx = self.page = None
        self.text = ""
        self.dialogs = 0
        self._home = _Home()

    @_confined
    def start(self) -> None:
        try:
            from playwright.sync_api import sync_playwright
        except ImportError:
            raise DriverError("the web driver needs Playwright: uv pip install 'telic[ui]' && playwright install chromium") from None
        self._pw = sync_playwright().start()
        try:
            self._browser = self._pw.chromium.launch(headless=self.headless)
        except Exception as e:  # noqa: BLE001 - reported as the reason nothing ran
            self._pw.stop()
            self._pw = None
            first = str(e).strip().splitlines()[0] if str(e).strip() else type(e).__name__
            raise DriverError(f"cannot launch Chromium ({first}); run 'playwright install chromium'") from None

    def stop(self) -> None:
        self._home.call(self._stop)
        self._home.close()

    def _stop(self) -> None:
        for close in (lambda: self._ctx and self._ctx.close(), lambda: self._browser and self._browser.close(), lambda: self._pw and self._pw.stop()):
            try:
                close()
            except Exception:  # noqa: BLE001 - shutting down
                pass
        self._pw = self._browser = self._ctx = self.page = None

    @_confined
    def viewport(self, width: int, height: int) -> None:
        self.size = (width, height)
        if self.page is not None:
            self.page.set_viewport_size({"width": width, "height": height})

    @_confined
    def reset(self) -> None:
        if self._ctx is not None:
            self._ctx.close()
        w, h = self.size
        self._ctx = self._browser.new_context(viewport={"width": w, "height": h}, reduced_motion="reduce", service_workers="block")
        self._ctx.add_init_script(_WATCH_JS)
        self.page = self._ctx.new_page()
        self._ctx.on("page", lambda p: p.close())  # popups and new tabs leave the app
        self.page.on("dialog", self._on_dialog)
        self._goto()

    @_confined
    def reopen(self) -> None:
        self._goto()

    def _goto(self) -> None:
        try:
            self.page.goto(self.url, wait_until="load", timeout=30000)
        except Exception as e:  # noqa: BLE001 - the app did not load
            raise DriverError(f"cannot load {self.url}: {str(e).splitlines()[0]}") from None
        self._settle()

    def _on_dialog(self, d) -> None:
        self.dialogs += 1
        try:
            d.accept()
        except Exception:  # noqa: BLE001 - already handled
            pass

    def _settle(self) -> None:
        deadline = time.monotonic() + 10
        last = "no snapshot"
        while time.monotonic() < deadline:
            try:
                self.page.wait_for_load_state("load", timeout=self.timeout_ms * 3)
                self.page.evaluate(_QUIET_JS, [self.settle_ms, self.timeout_ms])
                self.text = self.page.aria_snapshot(mode="ai", timeout=self.timeout_ms)
                return
            except Exception as e:  # noqa: BLE001 - a navigation replaced the document; wait for the new one
                last = str(e).strip().splitlines()[0] if str(e).strip() else type(e).__name__
                time.sleep(0.05)
        raise DriverError(f"the page did not settle: {last}", moved=True)

    @_confined
    def screen(self) -> str:
        u = urlsplit(self.page.url)
        if f"{u.scheme}://{u.netloc}" != self.origin:
            return f"outside:{u.netloc or u.scheme}"
        frag = route(u.fragment) if u.fragment.startswith("/") and u.fragment != "/" else ""
        return route(u.path or "/") + (f"#{frag}" if frag else "")

    @_confined
    def observe(self) -> Snapshot:
        return Snapshot(self.screen(), parse_aria(self.text))

    @_confined
    def leaves(self, node: Node) -> bool:
        if not node.url:
            return False
        if node.url.startswith(("mailto:", "tel:", "sms:", "javascript:")):
            return True
        u = urlsplit(urljoin(self.page.url, node.url))
        return f"{u.scheme}://{u.netloc}" != self.origin

    def _loc(self, ref: str | None):
        if ref is None:
            raise DriverError("no element")
        return self.page.locator(f"aria-ref={ref}")

    def _hit(self, ref: str) -> dict:
        loc = self._loc(ref)
        got = loc.evaluate(_HIT_JS, "nearest", timeout=self.timeout_ms)
        if got["rendered"] and any(p[2] for p in got["points"]):
            got = loc.evaluate(_HIT_JS, "center", timeout=self.timeout_ms)
        return got

    @_confined
    def uncovered(self, node: Node) -> tuple[bool, list[tuple[str, str | None]]]:
        try:
            got = self._hit(node.ref or "")
        except Exception as e:  # noqa: BLE001 - detached between snapshot and test
            raise DriverError(f"cannot hit-test {node.label}: {str(e).splitlines()[0]}") from None
        return got["rendered"], [(f"{n} ({x}, {y})", who) for n, (x, y), who in got["points"]]

    @_confined
    def do(self, action: Action) -> None:
        before = self.page.url
        try:
            if action.kind == "key":
                self.page.keyboard.press(action.arg or "")
            else:
                if action.kind in ("click", "select"):
                    got = self._hit(action.ref or "")
                    center = got["points"][0][2] if got["points"] else "nothing: it is not rendered"
                    if center is not None and action.kind == "click":
                        raise DriverError(f"covered by {center}")
                loc = self._loc(action.ref)
                if action.kind == "click":
                    loc.click(timeout=self.timeout_ms)
                elif action.kind == "fill":
                    loc.fill(action.arg or "", timeout=self.timeout_ms)
                elif action.kind == "select":
                    loc.select_option(label=action.arg, timeout=self.timeout_ms)
                elif action.kind == "press":
                    loc.press(action.arg or "", timeout=self.timeout_ms)
        except DriverError:
            raise
        except Exception as e:  # noqa: BLE001 - the user could not do it
            raise DriverError(str(e).strip().splitlines()[0] if str(e).strip() else type(e).__name__, moved=True) from None
        self._settle()
        if self.screen().startswith("outside:"):
            raise DriverError(f"leaves the app (to {self.page.url} from {before})", moved=True)
