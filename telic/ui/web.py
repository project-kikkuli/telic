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
from .tree import TEXT_ENTRY, Action, Node, Snapshot, route

_LINE = re.compile(r"^(?P<indent>\s*)- (?P<body>.*)$")
_ATTR = re.compile(r"\s*\[(?P<a>[^\]]*)\]")
_ROLE = re.compile(r"[a-zA-Z]+")

_HIT_JS = """
(el, [block, visual]) => {
  // a person scrolls only what scrolls: a container with overflow hidden or clip keeps its offset
  const kept = [];
  const locked = (v) => v === 'hidden' || v === 'clip';
  const root = document.scrollingElement || document.documentElement;
  const rs = getComputedStyle(document.documentElement), bs = document.body ? getComputedStyle(document.body) : rs;
  const page = (a) => locked(rs[a]) || (rs[a] === 'visible' && locked(bs[a]));
  for (let p = el.parentElement; p; p = p.parentElement) {
    const cs = getComputedStyle(p);
    const box = p === root ? page : (a) => locked(cs[a]);
    if (p !== document.body) kept.push([p, box('overflowY') && p.scrollTop, box('overflowX') && p.scrollLeft]);
  }
  el.scrollIntoView({block, inline: 'nearest', behavior: 'instant'});
  for (const [p, top, left] of kept) {
    if (top !== false) p.scrollTop = top;
    if (left !== false) p.scrollLeft = left;
  }
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
  // behind a modal dialog that is not its own: not operable, so not "covered". A dialog
  // not marked modal counts only when it or its backdrop spans the viewport.
  const DIALOG = 'dialog[open], [role=dialog], [role=alertdialog]';
  const spans = (x) => { const b = x.getBoundingClientRect(); return b.left <= 1 && b.top <= 1 && b.right >= innerWidth - 1 && b.bottom >= innerHeight - 1; };
  const modal = (x) => x && (x.matches('dialog:modal, [aria-modal=true]') || spans(x));
  const top = document.elementFromPoint(pts[0][1], pts[0][2]);
  let blocker = null;
  if (top && !mine(top)) {
    const up = top.closest(DIALOG), down = top.querySelector && top.querySelector(DIALOG);
    blocker = modal(up) ? up : down && (modal(down) || spans(top)) ? down : null;
  }
  const behind = !!blocker && !blocker.contains(el);
  // painted over the point but letting the pointer through (pointer-events: none) still hides it
  const veil = (x, y) => {
    const st = document.createElement('style');
    st.textContent = '* { pointer-events: auto !important; }';
    document.documentElement.appendChild(st);
    const v = document.elementFromPoint(x, y);
    st.remove();
    if (!v || mine(v) || v.contains(el)) return null;
    for (let a = v; a && a.nodeType === 1; a = a.parentElement) {
      const cs = getComputedStyle(a);
      if (Number(cs.opacity) < 0.1 || cs.visibility !== 'visible') return null;
    }
    const cs = getComputedStyle(v);
    const alpha = (c) => { const m = c.match(/rgba?\\(([^)]*)\\)/); if (!m) return c === 'transparent' ? 0 : 1; const p = m[1].split(/[ ,\\/]+/).filter(Boolean); return p.length > 3 ? parseFloat(p[3]) : 1; };
    const paints = alpha(cs.backgroundColor) >= 0.1 || cs.backgroundImage !== 'none' || /^(IMG|VIDEO|CANVAS|svg|IFRAME)$/.test(v.tagName)
      || [...v.childNodes].some((c) => c.nodeType === 3 && c.textContent.trim());
    return paints ? describe(v) + ' (it lets clicks through, but it is painted over it)' : null;
  };
  return {rendered: true, behind, points: pts.map(([n, x, y]) => {
    if (x < 0 || y < 0 || x >= innerWidth || y >= innerHeight) return [n, [Math.round(x), Math.round(y)], 'the edge of the viewport (it is cut off)'];
    const h = document.elementFromPoint(x, y);
    return [n, [Math.round(x), Math.round(y)], mine(h) ? (visual ? veil(x, y) : null) : describe(h)];
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
  // A short timer is work in flight (a debounce, a fake network delay); one
  // set from inside such a timer is a polling loop, and is not waited for.
  // A longer one changes the app later by itself: when it is due is kept, so it can be waited for.
  const st = t.setTimeout = window.setTimeout, ct = window.clearTimeout, live = new Set(), later = t.later = new Map();
  let nested = 0;
  window.setTimeout = function (fn, ms, ...a) {
    const d = Number(ms) || 0;
    if (typeof fn === 'function' && d > 1000 && !nested) {
      const id = st.call(this, function () { later.delete(id); return fn.apply(this, a); }, ms);
      later.set(id, performance.now() + d);
      return id;
    }
    if (typeof fn !== 'function' || d > 1000 || nested) return st.call(this, fn, ms, ...a);
    t.pending++;
    const id = st.call(this, function () {
      if (live.delete(id)) t.pending--;
      nested++;
      try { return fn.apply(this, a); } finally { nested--; bump(); }
    }, ms);
    live.add(id);
    return id;
  };
  window.clearTimeout = function (id) {
    later.delete(id);
    if (live.delete(id)) { t.pending--; bump(); }
    return ct.call(this, id);
  };
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
    ((window.__telic && window.__telic.setTimeout) || setTimeout).call(window, tick, 8);
  };
  tick();
})
"""


# Milliseconds until the next timer the app set to change itself later, or null.
_LATER_JS = """
() => {
  const t = window.__telic;
  if (!t || !t.later || !t.later.size) return null;
  return Math.max(0, Math.min(...t.later.values()) - performance.now());
}
"""


# For a text field in a form: the name of the button that submits it ('' if only Enter does).
_FORM_JS = """
(el) => {
  const f = el.form || el.closest('form');
  if (!f) return null;
  const b = [...f.querySelectorAll('button, input[type=submit]')].find((b) => (b.type || 'submit') === 'submit');
  if (!b) return '';
  return (b.getAttribute('aria-label') || b.value && b.tagName === 'INPUT' && b.value || b.innerText || '').trim().replace(/\\s+/g, ' ');
}
"""


# Every function the page runs on an event (listeners, Svelte's delegated
# handlers, React's props) whose source names a watched variable. Evaluated
# with the DevTools command line API (getEventListeners).
_HANDLERS_JS = """
((names) => {
  const re = new RegExp('(^|[^\\w$])(' + names.join('|') + ')($|[^\\w$])');
  const fns = new Set();
  const add = (f) => {
    if (typeof f !== 'function' || fns.has(f)) return;
    let s;
    try { s = Function.prototype.toString.call(f); } catch (e) { return; }
    if (!s.includes('[native code]') && re.test(s)) fns.add(f);
  };
  for (const t of [window, document, ...document.querySelectorAll('*')]) {
    try { const ls = getEventListeners(t); for (const k in ls) for (const l of ls[k]) add(l.listener); } catch (e) {}
    if (t === window) continue;
    // handlers a framework keeps on the element: a function, [function, ...args], or {event: function}
    for (const k of [...Object.keys(t), ...Object.getOwnPropertySymbols(t)]) {
      let v;
      try { v = t[k]; } catch (e) { continue; }
      if (typeof v === 'function') add(v);
      else if (Array.isArray(v)) v.forEach(add);
      else if (v && typeof v === 'object' && (typeof k === 'symbol' || k.startsWith('__reactProps$'))) Object.values(v).forEach((x) => Array.isArray(x) ? x.forEach(add) : add(x));
    }
  }
  return [...fns];
})
"""

# A value as the model keeps it: scalars exactly, collections by size (0, 1,
# 2+: which items are data, as in the tree), records by their fields.
_ABSTRACT_JS = """
function () {
  'use strict';
  const abs = (v, depth) => {
    if (v === null || v === undefined) return String(v);
    const t = typeof v;
    if (t === 'boolean' || t === 'number') return v;
    if (t === 'string') return v.length <= 40 ? v : 'text';
    if (t !== 'object') return t;
    try {
      if ('v' in v && typeof v.f === 'number' && ('reactions' in v || 'wv' in v)) return abs(v.v, depth);  // a Svelte signal
      if (v instanceof Node || v === window) return 'element';
      const n = Array.isArray(v) ? v.length : v instanceof Map || v instanceof Set ? v.size : -1;
      if (n >= 0) return n === 0 ? '[0]' : n === 1 ? '[1]' : '[2+]';
      if (depth >= 2) return 'object';
      const out = {};
      for (const k of Object.keys(v).sort().slice(0, 24)) {
        let x;
        try { x = v[k]; } catch (e) { continue; }
        if (typeof x !== 'function') out[k] = abs(x, depth + 1);
      }
      return out;
    } catch (e) {
      return 'object';
    }
  };
  return abs(this, 0);
}
"""

# React keeps state in fibers, not closures: every stateful hook
# (useState, useReducer) of the function components named.
_FIBERS_JS = """
(names) => {
  const want = new Set(names), out = {}, seen = new Set();
  const abs = (ABSTRACT);
  for (const el of document.querySelectorAll('*')) {
    const k = Object.keys(el).find((k) => k.startsWith('__reactFiber$'));
    for (let f = k && el[k]; f; f = f.return) {
      if (seen.has(f) || (f.alternate && seen.has(f.alternate))) continue;
      seen.add(f);
      const name = f.type && (f.type.displayName || f.type.name);
      if (typeof f.type !== 'function' || !want.has(name)) continue;
      const vals = [];
      for (let h = f.memoizedState; h; h = h.next) if (h.queue && h.queue.lastRenderedReducer) vals.push(abs.call(h.memoizedState));
      (out[name] = out[name] || []).push(JSON.stringify(vals));
    }
  }
  return out;
}
""".replace("ABSTRACT", _ABSTRACT_JS.strip())


def _scalar(o: dict):
    """A primitive remote object's value as ``_ABSTRACT_JS`` keeps it, or None if it is an object."""
    t = o.get("type")
    if t == "undefined":
        return "undefined"
    if t == "object" and o.get("subtype") == "null":
        return "null"
    if t in ("boolean", "number"):
        return o.get("value", o.get("unserializableValue"))
    if t == "string":
        v = o.get("value", "")
        return v if len(v) <= 40 else "text"
    if t in ("function", "symbol", "bigint"):
        return t
    return None


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

    def __init__(self, url: str, *, settle_ms: int = 50, timeout_ms: int = 3000, headless: bool = True, wait_ms: int = 5000):
        self.url = url
        self.origin = "{0.scheme}://{0.netloc}".format(urlsplit(url))
        self.settle_ms = settle_ms
        self.wait_ms = wait_ms
        self.timeout_ms = timeout_ms
        self.headless = headless
        self.size = (1280, 800)
        self._pw = self._browser = self._ctx = self.page = None
        self.text = ""
        self.dialogs = 0
        self._home = _Home()
        self._watch: list = []
        self._cdp = None
        self._scripts: dict[str, str] = {}  # scriptId -> URL path
        self.read: set[str] = set()

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

    def watch(self, hidden: list) -> None:
        self._watch = list(hidden)

    def _debugger(self) -> None:
        """A DevTools session on the page, knowing which file each script is."""
        self._scripts = {}
        self._cdp = self._ctx.new_cdp_session(self.page)
        self._cdp.on("Debugger.scriptParsed", lambda e: self._scripts.__setitem__(e["scriptId"], urlsplit(e.get("url") or "").path))
        self._cdp.send("Debugger.enable")
        self._cdp.send("Debugger.setSkipAllPauses", {"skip": True})
        self._cdp.send("Runtime.enable")

    def _hidden(self) -> dict[str, list] | None:
        """The watched variables' values now: from the scopes of the page's
        handlers (and of the getters of objects they hold), matched by name
        and by the file the function is in, and from React's fibers."""
        if not self._watch or self._cdp is None:
            return None
        cdp = self._cdp
        want: dict[str, list] = {}
        for h in self._watch:
            if not h.react:
                want.setdefault(h.name, []).append(h)
        got: dict[str, set[str]] = {}

        def owner(fn_id: str) -> tuple[str, str | None]:
            props = cdp.send("Runtime.getProperties", {"objectId": fn_id, "ownProperties": True})
            where, scopes = "", None
            for p in props.get("internalProperties", []):
                if p["name"] == "[[FunctionLocation]]":
                    where = self._scripts.get(p["value"]["value"]["scriptId"], "")
                elif p["name"] == "[[Scopes]]":
                    scopes = p["value"].get("objectId")
            return where, scopes

        def value(o: dict) -> str:
            v = _scalar(o)
            if v is None and o.get("objectId"):
                v = cdp.send("Runtime.callFunctionOn", {"objectId": o["objectId"], "functionDeclaration": _ABSTRACT_JS, "returnByValue": True, "objectGroup": "telic"})["result"].get("value")
            return json.dumps(v, sort_keys=True)

        try:
            if want:
                arr = cdp.send(
                    "Runtime.evaluate", {"expression": f"({_HANDLERS_JS})({json.dumps(sorted(want))})", "includeCommandLineAPI": True, "objectGroup": "telic"}
                )["result"].get("objectId")
                fns = [p["value"]["objectId"] for p in cdp.send("Runtime.getProperties", {"objectId": arr, "ownProperties": True})["result"] if p["name"].isdigit()] if arr else []
                holders: list[str] = []  # objects in scope: their getters may hold state too
                for depth in range(2):
                    for fn in fns:
                        where, scopes = owner(fn)
                        if scopes is None:
                            continue
                        for sc in cdp.send("Runtime.getProperties", {"objectId": scopes, "ownProperties": True})["result"]:
                            obj = sc["value"]
                            if obj.get("description") == "Global" or not obj.get("objectId"):
                                continue
                            for var in cdp.send("Runtime.getProperties", {"objectId": obj["objectId"], "ownProperties": True})["result"]:
                                v = var.get("value") or {}
                                for h in want.get(var["name"], []):
                                    if where.endswith("/" + h.path):
                                        got.setdefault(f"{h.path}:{h.name}", set()).add(value(v))
                                if depth == 0 and v.get("type") == "object" and v.get("subtype") is None and v.get("objectId") and len(holders) < 64:
                                    holders.append(v["objectId"])
                    fns = []
                    for o in holders:
                        for p in cdp.send("Runtime.getProperties", {"objectId": o, "ownProperties": True, "accessorPropertiesOnly": True})["result"]:
                            g = (p.get("get") or {}).get("objectId")
                            if g:
                                fns.append(g)
                    holders = []
                    if not fns or all(f"{h.path}:{h.name}" in got for hs in want.values() for h in hs):
                        break
            comps = sorted({h.component for h in self._watch if h.react and h.component})
            if comps:
                fib = self.page.evaluate(_FIBERS_JS, comps)
                for h in self._watch:
                    if h.react and h.component in fib:
                        got.setdefault(f"{h.path}:{h.component}", set()).update(fib[h.component])
                        self.read.add(f"{h.path}:{h.name}")
        except Exception:  # noqa: BLE001 - navigating: read at the next snapshot
            return None
        finally:
            try:
                cdp.send("Runtime.releaseObjectGroup", {"objectGroup": "telic"})
            except Exception:  # noqa: BLE001 - the page went away
                pass
        self.read.update(f"{h.path}:{h.name}" for h in self._watch if not h.react and f"{h.path}:{h.name}" in got)
        return {k: sorted(v) for k, v in sorted(got.items())}

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
        if self._watch:
            self._debugger()
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

    def _settled(self, shown: str) -> None:
        """Settle; if nothing visible changed, look once more a little later
        (a handler that reacts after a frame or a short delay)."""
        self._settle()
        if self.text == shown:
            time.sleep(0.25)
            self._settle()

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
        root = parse_aria(self.text)
        for n in root.walk():
            if n.role in TEXT_ENTRY and n.ref is not None:
                try:
                    n.form = self._loc(n.ref).evaluate(_FORM_JS, timeout=self.timeout_ms)
                except Exception:  # noqa: BLE001 - detached since the snapshot: no form
                    n.form = None
        try:
            later = self.page.evaluate(_LATER_JS) if self.wait_ms else None
        except Exception:  # noqa: BLE001 - navigating: nothing pending in the new document yet
            later = None
        return Snapshot(self.screen(), root, int(later) + 1 if later is not None and later <= self.wait_ms else None, self._hidden())

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

    def _hit(self, ref: str, visual: bool = False) -> dict:
        """Where a pointer lands on it; ``visual``: also what is painted over it without taking the pointer."""
        loc = self._loc(ref)
        got = loc.evaluate(_HIT_JS, ["nearest", visual], timeout=self.timeout_ms)
        if got["rendered"] and any(p[2] for p in got["points"]):
            got = loc.evaluate(_HIT_JS, ["center", visual], timeout=self.timeout_ms)
        return got

    def _submit(self, action: Action) -> None:
        fields = json.loads(action.arg or "[]")
        for k, (ref, value) in enumerate(fields):
            got = self._hit(ref)
            if not got["rendered"] or got["points"][0][2] is not None:
                raise DriverError(f"a field of the form is {'covered by ' + got['points'][0][2] if got['rendered'] else 'not rendered'}", moved=k > 0)
            self._loc(ref).fill(value, timeout=self.timeout_ms)
        if action.ref is None:
            self._loc(fields[-1][0]).press("Enter", timeout=self.timeout_ms)
            return
        got = self._hit(action.ref)
        if not got["rendered"] or got["points"][0][2] is not None:
            raise DriverError(f"its button is {'covered by ' + got['points'][0][2] if got['rendered'] else 'not rendered'}", moved=True)
        self._loc(action.ref).click(timeout=self.timeout_ms)

    @_confined
    def uncovered(self, node: Node) -> tuple[bool, list[tuple[str, str | None]]]:
        try:
            got = self._hit(node.ref or "", True)
        except Exception as e:  # noqa: BLE001 - detached between snapshot and test
            raise DriverError(f"cannot hit-test {node.label}: {str(e).splitlines()[0]}") from None
        return got["rendered"] and not got.get("behind"), [(f"{n} ({x}, {y})", who) for n, (x, y), who in got["points"]]

    @_confined
    def do(self, action: Action) -> None:
        before, shown = self.page.url, self.text
        try:
            if action.kind == "key":
                self.page.keyboard.press(action.arg or "")
            elif action.kind == "wait":
                self.page.wait_for_timeout(int(action.arg or 0) + 50)
            else:
                if action.kind == "form":
                    self._submit(action)
                    self._settled(shown)
                    return
                # a user reaches an element by pointing at it (or tapping it) first
                got = self._hit(action.ref or "")
                if not got["rendered"]:
                    raise DriverError("not rendered (no size on screen)")
                center = got["points"][0][2]
                if center is not None:
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
        self._settled(shown)
        if self.screen().startswith("outside:"):
            raise DriverError(f"leaves the app (to {self.page.url} from {before})", moved=True)
