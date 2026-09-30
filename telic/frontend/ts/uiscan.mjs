// What an app's source says about its UI that the accessibility tree does
// not: the keys its handlers listen for, and the variables its handlers
// change that decide what renders.
// stdin: {"files": [{"path", "text"}]}
// stdout: {"keys": [{"key", "path", "line"}], "state": [{"name", "path", "line", "writes", "reads", "component", "react"}]}

import { createRequire } from "node:module";
import fs from "node:fs";

const require = createRequire(import.meta.url);
const ts = require("typescript");

const isFn = (n) =>
  ts.isFunctionDeclaration(n) || ts.isFunctionExpression(n) || ts.isArrowFunction(n) || ts.isMethodDeclaration(n) ||
  ts.isGetAccessorDeclaration(n) || ts.isSetAccessorDeclaration(n) || ts.isConstructorDeclaration(n);
const strip = (e) => {
  while (e && (ts.isParenthesizedExpression(e) || ts.isAsExpression(e) || ts.isNonNullExpression(e) || ts.isTypeAssertionExpression(e) || (ts.isSatisfiesExpression && ts.isSatisfiesExpression(e)))) e = e.expression;
  return e;
};

// ---------------------------------------------------------------------------
// Keys, in the names Playwright presses them by

const MODS = { ctrl: "Control", control: "Control", cmd: "Meta", command: "Meta", meta: "Meta", super: "Meta", win: "Meta", mod: "ControlOrMeta", $mod: "ControlOrMeta", shift: "Shift", alt: "Alt", option: "Alt", opt: "Alt" };
const NAMED = {
  esc: "Escape", escape: "Escape", enter: "Enter", return: "Enter", space: "Space", spacebar: "Space", tab: "Tab", backspace: "Backspace",
  delete: "Delete", del: "Delete", up: "ArrowUp", down: "ArrowDown", left: "ArrowLeft", right: "ArrowRight", arrowup: "ArrowUp",
  arrowdown: "ArrowDown", arrowleft: "ArrowLeft", arrowright: "ArrowRight", home: "Home", end: "End", pageup: "PageUp", pagedown: "PageDown",
  insert: "Insert", plus: "+", comma: ",", slash: "/", period: ".", minus: "-", equal: "=", backquote: "`",
};
for (let i = 1; i <= 12; i++) NAMED[`f${i}`] = `F${i}`;
const CODES = { 8: "Backspace", 9: "Tab", 13: "Enter", 27: "Escape", 32: "Space", 33: "PageUp", 34: "PageDown", 35: "End", 36: "Home", 37: "ArrowLeft", 38: "ArrowUp", 39: "ArrowRight", 40: "ArrowDown", 46: "Delete", 191: "/", 188: ",", 190: "." };
for (let i = 0; i < 10; i++) CODES[48 + i] = String(i);
for (let i = 0; i < 26; i++) CODES[65 + i] = String.fromCharCode(97 + i);
for (let i = 1; i <= 12; i++) CODES[111 + i] = `F${i}`;

// An event's key value ('Escape', 'k', ' ') or code ('KeyK') as a key to press.
function keyName(v) {
  if (typeof v === "number") return CODES[v] || null;
  if (v === " ") return "Space";
  if (v.length === 1) return v;
  const low = v.toLowerCase();
  if (NAMED[low]) return NAMED[low];
  if (/^(Key[A-Z]|Digit\d|Numpad\w+|F\d{1,2}|Arrow(Up|Down|Left|Right)|Page(Up|Down)|Home|End|Insert|Delete|Backspace|Tab|Enter|Escape|Slash|Comma|Period|Minus|Equal|Backquote|Semicolon|Quote|Bracket(Left|Right)|Backslash)$/.test(v)) return v;
  return null;
}

// 'mod+shift+k', 'ctrl+K', 'Escape', 'shift+?' as written for a hotkey library.
function combo(s) {
  const t = s.trim();
  if (!t || /\s/.test(t)) return null; // sequences ('g i') are not one key
  const parts = t.endsWith("++") ? [...t.slice(0, -2).split("+"), "+"] : t.split("+");
  const key = keyName(parts.pop());
  if (!key || parts.some((p) => !MODS[p.toLowerCase()])) return null;
  const mods = [...new Set(parts.map((p) => MODS[p.toLowerCase()]))].sort();
  return [...mods, key].join("+");
}

const MOD_PROPS = { ctrlKey: "Control", metaKey: "Meta", shiftKey: "Shift", altKey: "Alt" };
const KEY_PROPS = new Set(["key", "code", "keyCode", "which", "charCode"]);
const KEY_EVENTS = new Set(["keydown", "keyup", "keypress"]);
const TIMERS = /(^|\.)(setInterval|setTimeout|requestAnimationFrame)$/;
const HOTKEY_CALL = /hotkey|shortcut|keybind|keymap|tinykeys|mousetrap/i;

// ---------------------------------------------------------------------------
// Single-file components: the script as TypeScript (other text blanked, so
// lines stay put) and the template's expressions

function blankExcept(text, ranges) {
  const out = text.split("").map((c) => (c === "\n" ? "\n" : " "));
  for (const [a, b] of ranges) for (let i = a; i < b; i++) out[i] = text[i];
  return out.join("");
}

function sfc(text) {
  const scripts = [];
  const re = /<script\b[^>]*>([\s\S]*?)<\/script>/g;
  let m;
  while ((m = re.exec(text))) scripts.push([m.index + m[0].indexOf(">") + 1, m.index + m[0].length - "</script>".length]);
  let markup = text.replace(/<script\b[^>]*>[\s\S]*?<\/script>|<style\b[^>]*>[\s\S]*?<\/style>|<!--[\s\S]*?-->/g, (s) => s.replace(/[^\n]/g, " "));
  return { script: blankExcept(text, scripts), markup };
}

function matchBrace(s, i) {
  let depth = 0;
  let q = null;
  for (let j = i; j < s.length; j++) {
    const c = s[j];
    if (q) {
      if (c === "\\") j++;
      else if (c === q) q = null;
      continue;
    }
    if (c === '"' || c === "'" || c === "`") q = c;
    else if (c === "{") depth++;
    else if (c === "}" && --depth === 0) return j;
  }
  return -1;
}

// Svelte: {#if e}, {:else if e}, {#each e as x}, {#key e}, name={e}, "…{e}…" in a tag, {e} in text.
function svelteExprs(markup) {
  const out = [];
  const lineAt = (i) => markup.slice(0, i).split("\n").length;
  let i = 0;
  while ((i = markup.indexOf("{", i)) >= 0) {
    const end = matchBrace(markup, i);
    if (end < 0) break;
    const inner = markup.slice(i + 1, end);
    const line = lineAt(i);
    const open = markup.lastIndexOf("<", i), close = markup.lastIndexOf(">", i);
    const inTag = open > close;
    let kind = "text", expr = inner, name = null;
    if (markup[i - 1] === "=") {
      let k = i - 2;
      while (k >= 0 && /[\w:.$|-]/.test(markup[k])) k--;
      name = markup.slice(k + 1, i - 1);
      kind = /^on/.test(name) ? "handler" : name === "bind:this" ? "skip" : name.startsWith("bind:") ? "bind" : "attr";
    } else if (inTag) {
      kind = /^\s*on\w+\s*$/.test(inner) ? "handler" : "attr";
      name = inner.trim();
    } else {
      const b = inner.match(/^\s*(#if|:else\s+if|#each|#key|#await|@html|@const|@render|[#:/@]\w*)\s*/);
      if (b) {
        const w = b[1];
        expr = inner.slice(b[0].length);
        if (w === "#each") expr = expr.replace(/\s+as\s+[\s\S]*$/, "");
        else if (w === "@const") expr = expr.replace(/^[^=]*=/, "");
        kind = ["#if", "#each", "#key", "#await", "@const", "@render"].includes(w) || /^:else\s+if/.test(w) ? "cond" : w === "@html" ? "text" : "skip";
      }
    }
    if (kind !== "skip" && expr.trim()) out.push({ kind, name, expr, line });
    i = end + 1;
  }
  return out;
}

// Vue: key modifiers on key listeners (@keydown.esc, v-on:keyup.ctrl.enter).
function vueKeys(markup, path, keys) {
  const re = /(?:@|v-on:)(keydown|keyup|keypress)((?:\.[\w-]+)+)/g;
  let m;
  while ((m = re.exec(markup))) {
    const mods = m[2].split(".").filter((x) => x && !["prevent", "stop", "self", "once", "capture", "passive", "exact"].includes(x));
    const k = combo(mods.join("+"));
    if (k) keys.push({ key: k, path, line: markup.slice(0, m.index).split("\n").length });
  }
}

// ---------------------------------------------------------------------------
// Scopes, by name: good enough to tell a component's variables from a
// handler's locals

class Scope {
  constructor(node, parent) {
    this.node = node;
    this.parent = parent;
    this.decls = new Map(); // name -> {node, kind, init, line, setter}
  }
  lookup(name) {
    for (let s = this; s; s = s.parent) if (s.decls.has(name)) return [s, s.decls.get(name)];
    return [null, null];
  }
}

function bindNames(b, into) {
  if (!b) return;
  if (ts.isIdentifier(b)) into.push(b);
  else if (b.elements) for (const el of b.elements) if (!ts.isOmittedExpression(el)) bindNames(el.name, into);
}

const STATEFUL_INIT = (e) => {
  e = strip(e);
  if (!e) return false;
  if (ts.isArrayLiteralExpression(e) || ts.isObjectLiteralExpression(e) || ts.isNewExpression(e)) return true;
  if (ts.isCallExpression(e)) {
    const c = e.expression.getText();
    return c === "$state" || c === "$state.raw";
  }
  return false;
};
const MUTATORS = new Set(["push", "pop", "shift", "unshift", "splice", "sort", "reverse", "fill", "set", "add", "delete", "clear", "copyWithin"]);

class Unit {
  constructor(path, component) {
    this.path = path;
    this.component = component; // a .svelte/.vue file, or a module with JSX
    this.render = new Set(); // names read where rendering is decided
    this.edges = []; // [from, to]: 'from' is read to compute 'to'
    this.writes = new Map(); // decl -> [lines]
    this.clock = new Map(); // decl -> [lines] written by a timer
    this.reads = new Map(); // name -> [lines] (render reads)
    this.state = []; // decls that can be state
    this.keys = [];
  }
}

function lineOf(sf, n, base = 0) {
  return sf.getLineAndCharacterOfPosition(n.getStart(sf)).line + 1 + base;
}

function analyze(unit, sf, fragments) {
  const root = new Scope(sf, null);
  const scopes = new Map(); // fn node -> Scope
  const fnDecls = new Map(); // name -> fn node, for handlers named by identifier

  // declarations of each function scope (hoisted), without descending into nested functions
  function declare(scope, body) {
    const visit = (n) => {
      if (ts.isVariableDeclaration(n)) {
        const ids = [];
        bindNames(n.name, ids);
        const list = n.parent;
        const isConst = list && (list.flags & ts.NodeFlags.Const) !== 0;
        const init = n.initializer ? strip(n.initializer) : null;
        const callee = init && ts.isCallExpression(init) ? init.expression.getText(sf) : "";
        if (/^\$props$|^\$bindable$/.test(callee)) return;
        const exported = list && list.parent && list.parent.modifiers && list.parent.modifiers.some((m) => m.kind === ts.SyntaxKind.ExportKeyword);
        let react = null;
        if (ts.isArrayBindingPattern(n.name) && init && ts.isCallExpression(init) && /^use[A-Z]\w*$|^React\.use\w+$/.test(callee)) {
          const els = n.name.elements.filter((e) => !ts.isOmittedExpression(e));
          if (els.length >= 2 && ts.isIdentifier(els[0].name) && ts.isIdentifier(els[1].name) && /^set[A-Z_$]/.test(els[1].name.text)) react = els[1].name.text;
        }
        for (const id of ids) {
          const d = { name: id.text, node: n, init, line: lineOf(sf, id), react: false, kind: "value" };
          if (react) {
            if (id.text === react) d.kind = "setter";
            else if (id === ids[0]) {
              d.kind = "state";
              d.react = true;
              d.setter = react;
            }
          } else if (/^\$derived/.test(callee)) d.kind = "derived";
          else if (!isConst && !(unit.path.endsWith(".svelte") && exported && scope === root)) d.kind = "state";
          else if (isConst && STATEFUL_INIT(init)) d.kind = "state";
          scope.decls.set(id.text, d);
        }
        if (n.initializer) visit(n.initializer);
        return;
      }
      if (ts.isFunctionDeclaration(n) && n.name) {
        scope.decls.set(n.name.text, { name: n.name.text, node: n, init: n, line: lineOf(sf, n.name), kind: "function" });
        fnDecls.set(n.name.text, n);
        return;
      }
      if (ts.isClassDeclaration(n) && n.name) {
        scope.decls.set(n.name.text, { name: n.name.text, node: n, init: null, line: lineOf(sf, n.name), kind: "class" });
        return;
      }
      if (isFn(n) || ts.isClassLike(n)) return;
      ts.forEachChild(n, visit);
    };
    ts.forEachChild(body, visit);
  }
  declare(root, sf);

  const scopeOf = (fn, parent) => {
    let s = scopes.get(fn);
    if (!s) {
      s = new Scope(fn, parent);
      for (const p of fn.parameters || []) {
        const ids = [];
        bindNames(p.name, ids);
        for (const id of ids) s.decls.set(id.text, { name: id.text, node: p, init: null, line: lineOf(sf, id), kind: "param" });
      }
      if (fn.body) declare(s, fn.body);
      for (const [name, d] of s.decls) if (d.kind === "function") fnDecls.set(name, d.node);
      scopes.set(fn, s);
    }
    return s;
  };

  const containsJsx = (n) => {
    let found = false;
    const v = (x) => {
      if (found) return;
      if (ts.isJsxElement(x) || ts.isJsxSelfClosingElement(x) || ts.isJsxFragment(x)) found = true;
      else ts.forEachChild(x, v);
    };
    v(n);
    return found;
  };

  // identifiers read in an expression (not property names, not declarations)
  const readsIn = (n, out = []) => {
    const v = (x) => {
      if (ts.isIdentifier(x)) {
        const p = x.parent;
        if (p && ts.isPropertyAccessExpression(p) && p.name === x) return;
        if (p && (ts.isPropertyAssignment(p) || ts.isMethodDeclaration(p) || ts.isPropertyDeclaration(p)) && p.name === x) return;
        if (p && (ts.isVariableDeclaration(p) || ts.isParameter(p) || ts.isFunctionDeclaration(p) || ts.isBindingElement(p)) && p.name === x) return;
        if (p && (ts.isJsxAttribute(p) || ts.isJsxOpeningElement(p) || ts.isJsxSelfClosingElement(p) || ts.isJsxClosingElement(p))) return;
        out.push(x);
        return;
      }
      if (ts.isShorthandPropertyAssignment(x)) {
        out.push(x.name);
        return;
      }
      ts.forEachChild(x, v);
    };
    v(n);
    return out;
  };

  const rootName = (e) => {
    e = strip(e);
    while (e && (ts.isPropertyAccessExpression(e) || ts.isElementAccessExpression(e))) e = strip(e.expression);
    return e && ts.isIdentifier(e) ? e : null;
  };

  // conditions guarding a node inside its function: if/?:/&&/|| tests up to the function
  const guards = (n) => {
    const out = [];
    for (let c = n, p = n.parent; p && !isFn(c); c = p, p = p.parent) {
      if (ts.isIfStatement(p) && p.expression !== c) out.push(p.expression);
      else if (ts.isConditionalExpression(p) && p.condition !== c) out.push(p.condition);
      else if (ts.isBinaryExpression(p) && p.right === c && [ts.SyntaxKind.AmpersandAmpersandToken, ts.SyntaxKind.BarBarToken, ts.SyntaxKind.QuestionQuestionToken].includes(p.operatorToken.kind)) out.push(p.left);
      else if (ts.isCaseClause(p) && p.parent && p.parent.parent) out.push(p.parent.parent.expression, p.expression);
      else if ((ts.isWhileStatement(p) || ts.isForStatement(p)) && p.condition !== c && p.expression !== c) p.condition ? out.push(p.condition) : p.expression && out.push(p.expression);
    }
    return out;
  };

  // inside a function a timer calls: the app changes by itself, not on a handler
  const timed = (n) => {
    let f = n.parent;
    while (f && !isFn(f)) f = f.parent;
    const c = f && f.parent;
    return !!(c && ts.isCallExpression(c) && c.arguments.includes(f) && TIMERS.test(c.expression.getText(sf)));
  };
  const note = (d, n) => {
    const into = timed(n) ? unit.clock : unit.writes;
    if (!into.has(d)) into.set(d, []);
    into.get(d).push(lineOf(sf, n));
  };

  const write = (scope, id, n, fnDepth) => {
    const [s, d] = scope.lookup(id.text);
    if (!d) return;
    // a write that runs after the declaration's own scope has: a handler or an effect
    if (fnDepth > 0 && s !== scope) note(d, n);
    for (const g of guards(n)) for (const r of readsIn(g)) unit.edges.push([r.text, d.name]);
  };

  const renderRead = (n, sfx, base) => {
    for (const r of readsIn(n)) {
      unit.render.add(r.text);
      if (!unit.reads.has(r.text)) unit.reads.set(r.text, []);
      unit.reads.get(r.text).push(lineOf(sfx, r, base));
    }
  };

  // the functions that handle key events, then the keys they compare against
  const keyHandlers = [];
  const hotkeyCall = (call) => {
    const c = call.expression;
    const name = ts.isIdentifier(c) ? c.text : ts.isPropertyAccessExpression(c) ? `${c.expression.getText(sf)}.${c.name.text}` : "";
    if (!HOTKEY_CALL.test(name)) return;
    const add = (s, at) => {
      for (const part of s.split(/(?<=[^+\s])\s*,\s*(?=[^\s])/)) {
        const k = combo(part);
        if (k) unit.keys.push({ key: k, path: unit.path, line: lineOf(sf, at) });
      }
    };
    for (const a0 of call.arguments) {
      const a = strip(a0);
      if (ts.isStringLiteralLike(a)) add(a.text, a);
      else if (ts.isArrayLiteralExpression(a)) for (const e of a.elements) ts.isStringLiteralLike(e) && add(e.text, e);
      else if (ts.isObjectLiteralExpression(a))
        for (const p of a.properties) {
          const k = p.name && (ts.isIdentifier(p.name) || ts.isStringLiteralLike(p.name)) ? p.name.text : null;
          if (k) add(k, p);
        }
    }
  };

  const walk = (n, scope, fnDepth, jsxFn) => {
    if (isFn(n)) {
      const s = scopeOf(n, scope);
      const component = unit.component && !jsxFn && fnDepth === 0 && n.body && containsJsx(n.body) ? n : jsxFn;
      ts.forEachChild(n, (c) => walk(c, s, fnDepth + (component === n && jsxFn !== n ? 0 : 1), component));
      return;
    }
    if (ts.isBinaryExpression(n) && n.operatorToken.kind >= ts.SyntaxKind.FirstAssignment && n.operatorToken.kind <= ts.SyntaxKind.LastAssignment) {
      const id = rootName(n.left);
      if (id) {
        write(scope, id, n, fnDepth);
        const [, d] = scope.lookup(id.text);
        if (d) for (const r of readsIn(n.right)) unit.edges.push([r.text, d.name]);
      }
    } else if ((ts.isPrefixUnaryExpression(n) || ts.isPostfixUnaryExpression(n)) && [ts.SyntaxKind.PlusPlusToken, ts.SyntaxKind.MinusMinusToken].includes(n.operator)) {
      const id = rootName(n.operand);
      if (id) write(scope, id, n, fnDepth);
    } else if (ts.isDeleteExpression(n)) {
      const id = rootName(n.expression);
      if (id) write(scope, id, n, fnDepth);
    } else if (ts.isCallExpression(n)) {
      const c = strip(n.expression);
      if (ts.isPropertyAccessExpression(c) && MUTATORS.has(c.name.text)) {
        const id = rootName(c.expression);
        if (id) {
          write(scope, id, n, fnDepth);
          const [, d] = scope.lookup(id.text);
          if (d) for (const a of n.arguments) for (const r of readsIn(a)) unit.edges.push([r.text, d.name]);
        }
      }
      if (ts.isIdentifier(c)) {
        // a React setter: setX(v)
        const [, d] = scope.lookup(c.text);
        if (d && d.kind === "setter") {
          const [s2, st] = scope.lookup(d.node && d.node.name && d.node.name.elements ? d.node.name.elements[0].name.text : "");
          if (st) {
            if (fnDepth > 0) note(st, n);
            for (const a of n.arguments) for (const r of readsIn(a)) unit.edges.push([r.text, st.name]);
            for (const g of guards(n)) for (const r of readsIn(g)) unit.edges.push([r.text, st.name]);
          }
        }
      }
      // addEventListener('keydown', h)
      if (ts.isPropertyAccessExpression(c) && c.name.text === "addEventListener" && n.arguments.length >= 2) {
        const t = strip(n.arguments[0]);
        if (ts.isStringLiteralLike(t) && KEY_EVENTS.has(t.text)) keyHandlers.push([n.arguments[1], scope]);
      }
      hotkeyCall(n);
    } else if (ts.isJsxAttribute(n) && n.initializer && ts.isJsxExpression(n.initializer) && n.initializer.expression) {
      const name = n.name.getText(sf);
      if (/^on[A-Z]/.test(name)) {
        if (/^onKey(Down|Up|Press)$/.test(name)) keyHandlers.push([n.initializer.expression, scope]);
      } else if (jsxFn) renderRead(n.initializer.expression, sf, 0);
    } else if (ts.isJsxExpression(n) && n.expression && !(n.parent && ts.isJsxAttribute(n.parent))) {
      if (jsxFn) renderRead(n.expression, sf, 0);
    } else if (ts.isLabeledStatement(n) && n.label.text === "$" && unit.path.endsWith(".svelte")) {
      // Svelte 4: `$: x = e` is derived, not a handler write
      const st = n.statement;
      const e = ts.isExpressionStatement(st) ? strip(st.expression) : null;
      if (e && ts.isBinaryExpression(e) && e.operatorToken.kind === ts.SyntaxKind.EqualsToken) {
        const id = rootName(e.left);
        if (id) for (const r of readsIn(e.right)) unit.edges.push([r.text, id.text]);
        return;
      }
      for (const r of readsIn(st)) unit.render.add(r.text);
      return;
    }
    // `el.onkeydown = h`
    if (ts.isBinaryExpression(n) && n.operatorToken.kind === ts.SyntaxKind.EqualsToken && ts.isPropertyAccessExpression(n.left) && /^onkey(down|up|press)$/.test(n.left.name.text)) keyHandlers.push([n.right, scope]);
    // component bodies decide what renders in their conditions
    if (jsxFn && fnDepth === 0 && (ts.isIfStatement(n) || ts.isConditionalExpression(n) || ts.isSwitchStatement(n))) renderRead(ts.isIfStatement(n) || ts.isSwitchStatement(n) ? n.expression : n.condition, sf, 0);
    // a module that is not a component: every read of state counts (it can reach the page any way)
    if (!unit.component && ts.isIdentifier(n)) {
      const refs = readsIn(n);
      if (refs.length) {
        const p = n.parent;
        const own = p && ((ts.isBinaryExpression(p) && p.left === n && p.operatorToken.kind === ts.SyntaxKind.EqualsToken) || ts.isPrefixUnaryExpression(p) || ts.isPostfixUnaryExpression(p));
        if (!own) {
          unit.render.add(n.text);
          if (!unit.reads.has(n.text)) unit.reads.set(n.text, []);
          unit.reads.get(n.text).push(lineOf(sf, n));
        }
      }
    }
    ts.forEachChild(n, (c) => walk(c, scope, fnDepth, jsxFn));
  };
  walk(sf, root, 0, null);

  // initializers of derived values and bodies of functions: what they read flows into them
  const allScopes = [root, ...scopes.values()];
  for (const s of allScopes)
    for (const d of s.decls.values()) {
      if (d.kind === "function" && d.node.body) for (const r of readsIn(d.node.body)) unit.edges.push([r.text, d.name]);
      else if (d.init && d.kind !== "setter") {
        for (const r of readsIn(d.init)) unit.edges.push([r.text, d.name]);
        if (isFn(d.init) && d.init.body) for (const r of readsIn(d.init.body)) unit.edges.push([r.text, d.name]);
      }
      if (d.kind === "state" && (s === root || s.node !== sf)) unit.state.push([s, d]);
    }

  // the template: conditions and attributes render; handlers write; bind: writes
  for (const f of fragments || []) {
    const fsf = ts.createSourceFile(unit.path + ".expr.ts", "(" + f.expr + "\n)", ts.ScriptTarget.Latest, true, ts.ScriptKind.TS);
    const e = fsf.statements[0] && ts.isExpressionStatement(fsf.statements[0]) ? fsf.statements[0].expression : null;
    if (!e) continue;
    const base = f.line - 1;
    if (f.kind === "cond" || f.kind === "attr") {
      for (const r of readsIn(e)) {
        unit.render.add(r.text);
        if (!unit.reads.has(r.text)) unit.reads.set(r.text, []);
        unit.reads.get(r.text).push(lineOf(fsf, r, base));
      }
    }
    if (f.kind === "bind") {
      const id = rootName(e);
      const [, d] = id ? root.lookup(id.text) : [null, null];
      if (d) {
        if (!unit.writes.has(d)) unit.writes.set(d, []);
        unit.writes.get(d).push(f.line);
        unit.render.add(d.name);
      }
    }
    if (f.kind === "handler") {
      // writes inside the handler's functions, against the script's scope
      const lineFix = (n) => lineOf(fsf, n, base);
      const hw = (n, depth) => {
        if (isFn(n)) return ts.forEachChild(n, (c) => hw(c, depth + 1));
        let id = null;
        if (ts.isBinaryExpression(n) && n.operatorToken.kind >= ts.SyntaxKind.FirstAssignment && n.operatorToken.kind <= ts.SyntaxKind.LastAssignment) {
          id = rootName(n.left);
          if (id) {
            const [, d] = root.lookup(id.text);
            if (d) for (const r of readsIn(n.right)) unit.edges.push([r.text, d.name]);
          }
        } else if ((ts.isPrefixUnaryExpression(n) || ts.isPostfixUnaryExpression(n)) && [ts.SyntaxKind.PlusPlusToken, ts.SyntaxKind.MinusMinusToken].includes(n.operator)) id = rootName(n.operand);
        else if (ts.isCallExpression(n) && ts.isPropertyAccessExpression(strip(n.expression)) && MUTATORS.has(strip(n.expression).name.text)) id = rootName(strip(n.expression).expression);
        if (id && depth > 0) {
          const [, d] = root.lookup(id.text);
          if (d) {
            if (!unit.writes.has(d)) unit.writes.set(d, []);
            unit.writes.get(d).push(lineFix(n));
            for (const g of guards(n)) for (const r of readsIn(g)) unit.edges.push([r.text, d.name]);
          }
        }
        ts.forEachChild(n, (c) => hw(c, depth));
      };
      hw(e, 0);
      if (/^on:?key(down|up|press)$/.test(f.name || "")) keyHandlers.push([e, root, fsf, base]);
    }
  }

  // keys: comparisons in each key handler (and the functions of this file it calls)
  const seen = new Set();
  const keysIn = (body, sfx, base, depth) => {
    if (!body || seen.has(body) || depth > 3) return;
    seen.add(body);
    const mods = (n) => {
      const out = new Set();
      const collect = (x, neg) => {
        if (ts.isPrefixUnaryExpression(x) && x.operator === ts.SyntaxKind.ExclamationToken) return collect(x.operand, !neg);
        if (ts.isPropertyAccessExpression(x) && MOD_PROPS[x.name.text] && !neg) out.add(MOD_PROPS[x.name.text]);
        if (isFn(x)) return;
        ts.forEachChild(x, (c) => collect(c, neg));
      };
      for (const g of [n, ...guards(n)]) {
        let top = g;
        while (top.parent && (ts.isParenthesizedExpression(top.parent) || (ts.isBinaryExpression(top.parent) && [ts.SyntaxKind.AmpersandAmpersandToken, ts.SyntaxKind.BarBarToken].includes(top.parent.operatorToken.kind)))) top = top.parent;
        collect(top, false);
      }
      if (out.has("Control") && out.has("Meta")) {
        out.delete("Control");
        out.delete("Meta");
        out.add("ControlOrMeta");
      }
      return [...out].sort();
    };
    const keyProp = (x) => {
      x = strip(x);
      while (x && ts.isCallExpression(x) && ts.isPropertyAccessExpression(x.expression) && /^to(Lower|Upper)Case$/.test(x.expression.name.text)) x = strip(x.expression.expression);
      return x && ts.isPropertyAccessExpression(x) && KEY_PROPS.has(x.name.text);
    };
    const lit = (x) => {
      x = strip(x);
      if (ts.isStringLiteralLike(x)) return x.text;
      if (ts.isNumericLiteral(x)) return Number(x.text);
      return null;
    };
    const add = (v, at) => {
      const k = v === null ? null : keyName(v);
      if (k) unit.keys.push({ key: [...mods(at), k].join("+"), path: unit.path, line: lineOf(sfx, at, base) });
    };
    const v = (n) => {
      if (ts.isBinaryExpression(n) && [ts.SyntaxKind.EqualsEqualsEqualsToken, ts.SyntaxKind.EqualsEqualsToken].includes(n.operatorToken.kind)) {
        if (keyProp(n.left)) add(lit(n.right), n);
        else if (keyProp(n.right)) add(lit(n.left), n);
      } else if (ts.isSwitchStatement(n) && keyProp(n.expression)) {
        for (const c of n.caseBlock.clauses) if (ts.isCaseClause(c)) add(lit(c.expression), c);
      } else if (ts.isCallExpression(n) && ts.isPropertyAccessExpression(n.expression) && n.expression.name.text === "includes" && n.arguments[0] && keyProp(n.arguments[0])) {
        const arr = strip(n.expression.expression);
        if (ts.isArrayLiteralExpression(arr)) for (const e of arr.elements) add(lit(e), n);
      } else if (ts.isCallExpression(n) && ts.isIdentifier(n.expression) && fnDecls.has(n.expression.text)) {
        const f = fnDecls.get(n.expression.text);
        if (f.getSourceFile() === sf) keysIn(f.body, sf, 0, depth + 1);
      }
      ts.forEachChild(n, v);
    };
    v(body);
  };
  for (const [h0, scope, fsf, base] of keyHandlers) {
    const h = strip(h0);
    if (isFn(h)) keysIn(h.body, fsf || sf, base || 0, 0);
    else if (ts.isIdentifier(h)) {
      const [, d] = scope.lookup(h.text);
      const f = d && (d.kind === "function" ? d.node : d.init && isFn(d.init) ? d.init : null);
      if (f) keysIn(f.body, sf, 0, 0);
    }
  }
  return unit;
}

// ---------------------------------------------------------------------------

function scanFile(path, text) {
  const svelte = path.endsWith(".svelte"), vue = path.endsWith(".vue");
  let src = text, fragments = null;
  const keys = [];
  if (svelte || vue) {
    const parts = sfc(text);
    src = parts.script;
    fragments = svelte ? svelteExprs(parts.markup) : [];
    if (vue) vueKeys(parts.markup, path, keys);
  }
  const kind = /\.(tsx|jsx)$/.test(path) ? ts.ScriptKind.TSX : /\.(js|mjs|cjs)$/.test(path) ? ts.ScriptKind.JSX : ts.ScriptKind.TS;
  const sf = ts.createSourceFile(path, src, ts.ScriptTarget.Latest, true, kind);
  const hasJsx = /\.(tsx|jsx|js)$/.test(path) && /<[A-Za-z>]/.test(src) && (() => {
    let f = false;
    const v = (n) => {
      if (f) return;
      if (ts.isJsxElement(n) || ts.isJsxSelfClosingElement(n) || ts.isJsxFragment(n)) f = true;
      else ts.forEachChild(n, v);
    };
    v(sf);
    return f;
  })();
  const unit = analyze(new Unit(path, svelte || vue || hasJsx), sf, fragments);
  unit.keys.push(...keys);
  // what decides rendering, and everything that flows into it
  const influence = new Set(unit.render);
  let grew = true;
  while (grew) {
    grew = false;
    for (const [a, b] of unit.edges)
      if (influence.has(b) && !influence.has(a)) {
        influence.add(a);
        grew = true;
      }
  }
  const state = [];
  for (const [s, d] of unit.state) {
    const w = unit.writes.get(d);
    if (!w || !influence.has(d.name)) continue;
    const reads = unit.reads.get(d.name) || [];
    let component = null;
    for (let x = s.node; x && x !== sf; x = x.parent) {
      if (isFn(x) && x.name) {
        component = x.name.getText(sf);
        break;
      }
      if (ts.isVariableDeclaration(x) && ts.isIdentifier(x.name)) {
        component = x.name.text;
        break;
      }
    }
    const clock = unit.clock.get(d);
    state.push({ name: d.name, path, line: d.line, clock: clock ? [...new Set(clock)].sort((a, b) => a - b).slice(0, 3) : [], writes: [...new Set(w)].sort((a, b) => a - b).slice(0, 3), reads: [...new Set(reads)].sort((a, b) => a - b).slice(0, 3), component, react: !!d.react });
  }
  return { keys: unit.keys, state };
}

const input = JSON.parse(fs.readFileSync(0, "utf8"));
const out = { keys: [], state: [], errors: [] };
for (const f of input.files) {
  try {
    const got = scanFile(f.path, f.text);
    out.keys.push(...got.keys);
    out.state.push(...got.state);
  } catch (e) {
    out.errors.push(`${f.path}: ${String(e && e.message || e).split("\n")[0]}`);
  }
}
process.stdout.write(JSON.stringify(out));
