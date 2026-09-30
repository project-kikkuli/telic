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
// Attributes whose value the accessibility tree shows as it is (a name, a
// state, a value) rather than deciding which elements exist or can be used.
const CONTENT_ATTRS = new Set([
  "value", "checked", "selected", "title", "alt", "placeholder", "label", "defaultValue", "defaultChecked", "datetime",
  "aria-label", "aria-labelledby", "aria-describedby", "aria-description", "aria-expanded", "aria-pressed", "aria-checked",
  "aria-selected", "aria-current", "aria-valuenow", "aria-valuetext", "aria-valuemin", "aria-valuemax", "aria-placeholder",
  "ariaLabel", "ariaExpanded", "ariaPressed", "ariaChecked", "ariaSelected", "ariaCurrent",
]);
// What a live region says is an announcement, not state (as the tree keeps it).
const LIVE_ATTRS = /\baria-live\s*=\s*["']?(polite|assertive)|\brole\s*=\s*["']?(status|alert|log|marquee|timer)\b/;
const VOID = new Set(["area", "base", "br", "col", "embed", "hr", "img", "input", "link", "meta", "source", "track", "wbr"]);
// the class of a read at an attribute: content, or structure (which elements exist, their roles, whether they can be used)
const attrClass = (tag, name) => (/^[A-Z]|[.:]/.test(tag || "") && !/^svelte:(window|document|body|head)$/.test(tag) ? "structure" : CONTENT_ATTRS.has(name) || name.startsWith("bind:value") || name === "bind:checked" || name === "bind:group" ? "content" : "structure");

// The elements open at each position of a template: [{tag, attrs}] per offset asked for.
function openAt(markup) {
  const events = [];
  const re = /<(\/?)([A-Za-z][\w:.-]*)((?:[^>"'{]|"[^"]*"|'[^']*'|\{[^}]*\})*?)(\/?)>/g;
  let m;
  while ((m = re.exec(markup))) events.push({ at: m.index, close: !!m[1], tag: m[2], attrs: m[3], self: !!m[4] || VOID.has(m[2].toLowerCase()) });
  return (i) => {
    const stack = [];
    for (const e of events) {
      if (e.at >= i) break;
      if (e.close) {
        const k = stack.map((x) => x.tag).lastIndexOf(e.tag);
        if (k >= 0) stack.length = k;
      } else if (!e.self) stack.push(e);
    }
    return stack;
  };
}
const liveIn = (stack) => stack.some((e) => LIVE_ATTRS.test(e.attrs));

// a function that takes its keys as arguments: its call sites spell them out
const HOTKEY_API = /^(use|create|register|add|bind)?(hot)?key(s|board)?(bindings?|shortcuts?|map)?$|^(use|create|register|add)?shortcuts?$|^tinykeys$|^(mousetrap|Mousetrap)\.bind$/i;

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
  const opened = openAt(markup);
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
    const tag = inTag ? (markup.slice(open + 1).match(/^[\w:.-]+/) || [""])[0] : null;
    if (kind !== "skip" && expr.trim()) out.push({ kind, name, expr, line, tag, live: kind === "text" && liveIn(opened(i)) });
    i = end + 1;
  }
  return out;
}

// Vue: v-if/v-else-if/v-show/v-for decide, :attr and v-bind render, @event
// and v-on handle (as statements), v-model binds, {{ e }} is text.
function vueExprs(markup) {
  const out = [];
  const lineAt = (i) => markup.slice(0, i).split("\n").length;
  const opened = openAt(markup);
  const tag = /<([A-Za-z][\w.-]*)((?:[^>"']|"[^"]*"|'[^']*')*)>/g;
  let t;
  while ((t = tag.exec(markup))) {
    const attrs = t[2], at = t.index + 1 + t[1].length, el = t[1];
    const re = /([@:#]?[\w.:\[\]-]+)\s*=\s*(?:"([^"]*)"|'([^']*)')/g;
    let a;
    while ((a = re.exec(attrs))) {
      const name = a[1], expr = a[2] !== undefined ? a[2] : a[3], line = lineAt(at + a.index);
      if (/^v-(if|else-if|show)$/.test(name)) out.push({ kind: "cond", name, expr, line });
      else if (name === "v-for") out.push({ kind: "cond", name, expr: expr.replace(/^[\s\S]*?\s+(in|of)\s+/, ""), line });
      else if (name === "v-model" || name.startsWith("v-model:")) out.push({ kind: "bind", name: /^[A-Z]|-/.test(el) ? "bind:model" : "bind:value", expr, line, tag: el });
      else if (name[0] === "@" || name.startsWith("v-on:")) {
        const ev = name.replace(/^(@|v-on:)/, "").split(".")[0];
        const fn = /^\s*[\w$.]+\s*$/.test(expr) || /=>|^\s*(async\s+)?function\b/.test(expr);
        out.push({ kind: "handler", name: `on${ev}`, expr, line, inline: !fn });
      } else if (name[0] === ":" || name.startsWith("v-bind")) out.push({ kind: "attr", name: name.replace(/^(:|v-bind:?)/, ""), expr, line, tag: el });
    }
  }
  const mu = /\{\{([\s\S]*?)\}\}/g;
  let m;
  while ((m = mu.exec(markup))) out.push({ kind: "text", name: null, expr: m[1], line: lineAt(m.index), live: liveIn(opened(m.index)) });
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

// reactive containers a handler changes through a method or `.value`: Svelte runes and stores, Vue refs
const STATE_CALL = /^(\$state|\$state\.raw|(\w+\.)?(writable|readable|ref|shallowRef|customRef|reactive|shallowReactive|toRef|useStorage|useLocalStorage|useSessionStorage))$/;
const DERIVED_CALL = /^(\$derived(\.by)?|(\w+\.)?(derived|computed))$/;
const STATEFUL_INIT = (e) => {
  e = strip(e);
  if (!e) return false;
  if (ts.isArrayLiteralExpression(e) || ts.isObjectLiteralExpression(e) || ts.isNewExpression(e)) return true;
  return ts.isCallExpression(e) && STATE_CALL.test(e.expression.getText());
};
const MUTATORS = new Set(["push", "pop", "shift", "unshift", "splice", "sort", "reverse", "fill", "set", "add", "delete", "clear", "copyWithin", "update"]);
const STORAGE = /^(window\.)?(localStorage|sessionStorage)$/;
const STORAGE_WRITES = new Set(["setItem", "removeItem", "clear"]);
const DATABASES = /^(window\.)?indexedDB$|^(Dexie|localforage|openDB|idb|createStore)$/;

class Unit {
  constructor(path, component) {
    this.path = path;
    this.component = component; // a .svelte/.vue file, or a module with JSX
    this.render = new Set(); // names read where it is decided which elements exist, their roles, whether they can be used
    this.content = new Set(); // names read where only what the tree shows of an element (a name, a state, a value) is decided
    this.edges = []; // [from, to]: 'from' is read to compute 'to'
    this.writes = new Map(); // decl -> [lines]
    this.clock = new Map(); // decl -> [lines] written by a timer
    this.reads = new Map(); // name -> [lines] (render reads)
    this.state = []; // decls that can be state
    this.keys = [];
    this.imports = new Map(); // local name -> {from, name}: name is 'default', '*' or the exported name
    this.exports = new Map(); // exported name -> local name
    this.xwrites = []; // [local import name, property (for '* as m'), line, timed]: a handler changes another module's state
    this.storage = []; // {api, line, write}
    this.unresolved = []; // {line, why}: a key handler reacts to keys the source does not spell out
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
      if (ts.isImportDeclaration(n) && ts.isStringLiteralLike(n.moduleSpecifier) && n.importClause) {
        const from = n.moduleSpecifier.text, c = n.importClause;
        if (c.name) unit.imports.set(c.name.text, { from, name: "default" });
        const nb = c.namedBindings;
        if (nb && ts.isNamespaceImport(nb)) unit.imports.set(nb.name.text, { from, name: "*" });
        else if (nb) for (const e of nb.elements) unit.imports.set(e.name.text, { from, name: (e.propertyName || e.name).text });
        return;
      }
      if (ts.isExportDeclaration(n) && !n.moduleSpecifier && n.exportClause && ts.isNamedExports(n.exportClause)) {
        for (const e of n.exportClause.elements) unit.exports.set(e.name.text, (e.propertyName || e.name).text);
        return;
      }
      if (ts.isExportAssignment(n) && ts.isIdentifier(strip(n.expression))) unit.exports.set("default", strip(n.expression).text);
      if (scope === root && (ts.isVariableStatement(n) || ts.isFunctionDeclaration(n) || ts.isClassDeclaration(n)) && n.modifiers && n.modifiers.some((m) => m.kind === ts.SyntaxKind.ExportKeyword)) {
        const def = n.modifiers.some((m) => m.kind === ts.SyntaxKind.DefaultKeyword);
        if (ts.isVariableStatement(n))
          for (const v of n.declarationList.declarations) {
            const ids = [];
            bindNames(v.name, ids);
            for (const id of ids) unit.exports.set(id.text, id.text);
          }
        else if (n.name) unit.exports.set(def ? "default" : n.name.text, n.name.text);
      }
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
          } else if (DERIVED_CALL.test(callee)) d.kind = "derived";
          else if (!isConst && !(unit.path.endsWith(".svelte") && exported && scope === root)) d.kind = "state";
          else if (isConst && STATEFUL_INIT(init)) d.kind = "state";
          d.key = scope === root ? d.name : `${d.name}@${d.line}`;
          scope.decls.set(id.text, d);
        }
        if (n.initializer) visit(n.initializer);
        return;
      }
      if (ts.isFunctionDeclaration(n) && n.name) {
        scope.decls.set(n.name.text, { name: n.name.text, node: n, init: n, line: lineOf(sf, n.name), kind: "function", key: scope === root ? n.name.text : `${n.name.text}@${lineOf(sf, n.name)}` });
        fnDecls.set(n.name.text, n);
        return;
      }
      if (ts.isClassDeclaration(n) && n.name) {
        scope.decls.set(n.name.text, { name: n.name.text, node: n, init: null, line: lineOf(sf, n.name), kind: "class", key: scope === root ? n.name.text : `${n.name.text}@${lineOf(sf, n.name)}` });
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
        for (const id of ids) s.decls.set(id.text, { name: id.text, node: p, init: null, line: lineOf(sf, id), kind: "param", key: `${id.text}@${lineOf(sf, id)}` });
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

  // What an identifier names: a variable of this module by its name, one
  // inside a function by name and line (two `t`s are two variables), an
  // import or a global by its name.
  const binds = (f, name) => (f.parameters || []).some((p) => {
    const ids = [];
    bindNames(p.name, ids);
    return ids.some((i) => i.text === name);
  });
  const R = (r) => {
    const name = own(r.text);
    for (let p = r.parent; p; p = p.parent) {
      if (!isFn(p)) continue;
      if (scopes.has(p)) {
        const [, d] = scopes.get(p).lookup(name);
        return d ? d.key : name;
      }
      if (binds(p, name)) return `${name}@local`;
    }
    const [, d] = root.lookup(name);
    return d ? d.key : name;
  };
  // Svelte's `$store` is the store's value
  const svelte = unit.path.endsWith(".svelte");
  const own = (name) => (svelte && name.length > 1 && name[0] === "$" && (root.decls.has(name.slice(1)) || unit.imports.has(name.slice(1))) ? name.slice(1) : name);
  // a handler changing what another module declares: `state.tip = 1`, `store.update(f)`
  const foreign = (scope, id, n, line = (x) => lineOf(sf, x)) => {
    const [, d] = scope.lookup(id.text);
    const imp = !d && unit.imports.get(own(id.text));
    if (!imp) return false;
    const p = id.parent;
    const prop = imp.name === "*" && p && ts.isPropertyAccessExpression(p) && p.expression === id ? p.name.text : null;
    unit.xwrites.push([own(id.text), prop, line(n), timed(n)]);
    return true;
  };
  const write = (scope, id0, n, fnDepth) => {
    let id = id0;
    let [s, d] = scope.lookup(id.text);
    if (!d && own(id.text) !== id.text) [s, d] = scope.lookup(own(id.text));
    if (!d) {
      if (fnDepth > 0) foreign(scope, id, n);
      return;
    }
    // a write that runs after the declaration's own scope has: a handler or an effect
    if (fnDepth > 0 && s !== scope) note(d, n);
    for (const g of guards(n)) for (const r of readsIn(g)) unit.edges.push([R(r), d.key]);
  };

  const renderRead = (n, sfx, base, cls = "structure") => {
    for (const r of readsIn(n)) {
      unit[cls === "content" ? "content" : "render"].add(R(r));
      if (!unit.reads.has(r.text)) unit.reads.set(r.text, []);
      unit.reads.get(r.text).push(lineOf(sfx, r, base));
    }
  };

  // a JSX child that can only be text: a name, a property, a literal, a template of those
  const textOnly = (e) => {
    e = strip(e);
    if (ts.isIdentifier(e) || ts.isPropertyAccessExpression(e) || ts.isStringLiteralLike(e) || ts.isNumericLiteral(e)) return true;
    if (ts.isTemplateExpression(e)) return e.templateSpans.every((sp) => textOnly(sp.expression));
    if (ts.isBinaryExpression(e) && e.operatorToken.kind === ts.SyntaxKind.PlusToken) return textOnly(e.left) && textOnly(e.right);
    return false;
  };
  const liveJsx = (n) => {
    for (let p = n.parent; p && !isFn(p); p = p.parent) {
      const o = ts.isJsxElement(p) ? p.openingElement : null;
      if (o && o.attributes.properties.some((a) => ts.isJsxAttribute(a) && LIVE_ATTRS.test(a.getText(sf)))) return true;
    }
    return false;
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
    const before = unit.keys.length;
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
    if (unit.keys.length === before && call.arguments.length && HOTKEY_API.test(name)) unit.unresolved.push({ line: lineOf(sf, call), why: `${name} is given keys the source does not spell out` });
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
        if (d) for (const r of readsIn(n.right)) unit.edges.push([R(r), d.key]);
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
          if (d) for (const a of n.arguments) for (const r of readsIn(a)) unit.edges.push([R(r), d.key]);
        }
      }
      if (ts.isIdentifier(c)) {
        // a React setter: setX(v)
        const [, d] = scope.lookup(c.text);
        if (d && d.kind === "setter") {
          const [s2, st] = scope.lookup(d.node && d.node.name && d.node.name.elements ? d.node.name.elements[0].name.text : "");
          if (st) {
            if (fnDepth > 0) note(st, n);
            for (const a of n.arguments) for (const r of readsIn(a)) unit.edges.push([R(r), st.key]);
            for (const g of guards(n)) for (const r of readsIn(g)) unit.edges.push([R(r), st.key]);
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
      } else if (jsxFn) {
        const el = n.parent && n.parent.parent;
        const tag = el && (ts.isJsxOpeningElement(el) || ts.isJsxSelfClosingElement(el)) ? el.tagName.getText(sf) : "";
        renderRead(n.initializer.expression, sf, 0, attrClass(tag, name));
      }
    } else if (ts.isJsxExpression(n) && n.expression && !(n.parent && ts.isJsxAttribute(n.parent))) {
      if (jsxFn && !liveJsx(n)) renderRead(n.expression, sf, 0, textOnly(n.expression) ? "content" : "structure");
    } else if (ts.isLabeledStatement(n) && n.label.text === "$" && unit.path.endsWith(".svelte")) {
      // Svelte 4: `$: x = e` is derived, not a handler write
      const st = n.statement;
      const e = ts.isExpressionStatement(st) ? strip(st.expression) : null;
      if (e && ts.isBinaryExpression(e) && e.operatorToken.kind === ts.SyntaxKind.EqualsToken) {
        const id = rootName(e.left);
        if (id) for (const r of readsIn(e.right)) unit.edges.push([R(r), R(id)]);
        return;
      }
      for (const r of readsIn(st)) unit.render.add(R(r));
      return;
    }
    // storage the page keeps between actions (and reloads)
    if (ts.isIdentifier(n) || ts.isPropertyAccessExpression(n)) {
      const t = n.getText(sf);
      const p = n.parent;
      if (STORAGE.test(t) && !(p && ts.isPropertyAccessExpression(p) && p.name === n)) {
        const m = p && (ts.isPropertyAccessExpression(p) || ts.isElementAccessExpression(p)) && p.expression === n ? p : null;
        const assigned = m && m.parent && ts.isBinaryExpression(m.parent) && m.parent.left === m && m.parent.operatorToken.kind === ts.SyntaxKind.EqualsToken;
        const called = m && ts.isPropertyAccessExpression(m) && STORAGE_WRITES.has(m.name.text) && m.parent && ts.isCallExpression(m.parent);
        const deleted = m && m.parent && ts.isDeleteExpression(m.parent);
        unit.storage.push({ api: t.replace(/^window\./, ""), line: lineOf(sf, n), write: !!(assigned || called || deleted) });
      } else if (t === "document.cookie") {
        unit.storage.push({ api: "cookie", line: lineOf(sf, n), write: !!(p && ts.isBinaryExpression(p) && p.left === n) });
      } else if (DATABASES.test(t) && !(p && ts.isPropertyAccessExpression(p) && p.name === n)) {
        unit.storage.push({ api: "indexedDB", line: lineOf(sf, n), write: true });
      }
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
        const assigned = p && ((ts.isBinaryExpression(p) && p.left === n && p.operatorToken.kind === ts.SyntaxKind.EqualsToken) || ts.isPrefixUnaryExpression(p) || ts.isPostfixUnaryExpression(p));
        if (!assigned) {
          unit.render.add(R(n));
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
      if (d.kind === "function" && d.node.body) for (const r of readsIn(d.node.body)) unit.edges.push([R(r), d.key]);
      else if (d.init && d.kind !== "setter") {
        for (const r of readsIn(d.init)) unit.edges.push([R(r), d.key]);
        if (isFn(d.init) && d.init.body) for (const r of readsIn(d.init.body)) unit.edges.push([R(r), d.key]);
      }
      if (d.kind === "state" && (s === root || s.node !== sf)) unit.state.push([s, d]);
    }

  unit.declared = new Map();
  for (const s of allScopes) for (const name of s.decls.keys()) unit.declared.set(name, (unit.declared.get(name) || 0) + 1);

  // the template: conditions and attributes render; handlers write; bind: writes
  for (const f of fragments || []) {
    const fsf = ts.createSourceFile(unit.path + ".expr.ts", f.inline ? f.expr : "(" + f.expr + "\n)", ts.ScriptTarget.Latest, true, ts.ScriptKind.TS);
    const e = f.inline ? fsf : fsf.statements[0] && ts.isExpressionStatement(fsf.statements[0]) ? fsf.statements[0].expression : null;
    if (!e) continue;
    const base = f.line - 1;
    if (f.kind === "cond" || f.kind === "attr" || (f.kind === "text" && !f.live)) {
      const cls = f.kind === "text" ? "content" : f.kind === "attr" ? attrClass(f.tag, f.name) : "structure";
      for (const r of readsIn(e)) {
        const name = own(r.text);
        unit[cls === "content" ? "content" : "render"].add(R(r));
        if (!unit.reads.has(name)) unit.reads.set(name, []);
        unit.reads.get(name).push(lineOf(fsf, r, base));
      }
    }
    if (f.kind === "bind") {
      const id = rootName(e);
      const [, d] = id ? root.lookup(id.text) : [null, null];
      if (d) {
        if (!unit.writes.has(d)) unit.writes.set(d, []);
        unit.writes.get(d).push(f.line);
        unit[attrClass(f.tag, f.name) === "content" ? "content" : "render"].add(d.key);
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
            const [, d] = root.lookup(own(id.text));
            if (d) for (const r of readsIn(n.right)) unit.edges.push([R(r), d.key]);
          }
        } else if ((ts.isPrefixUnaryExpression(n) || ts.isPostfixUnaryExpression(n)) && [ts.SyntaxKind.PlusPlusToken, ts.SyntaxKind.MinusMinusToken].includes(n.operator)) id = rootName(n.operand);
        else if (ts.isCallExpression(n) && ts.isPropertyAccessExpression(strip(n.expression)) && MUTATORS.has(strip(n.expression).name.text)) id = rootName(strip(n.expression).expression);
        if (id && depth > 0) {
          const [, d] = root.lookup(own(id.text));
          if (d) {
            if (!unit.writes.has(d)) unit.writes.set(d, []);
            unit.writes.get(d).push(lineFix(n));
            for (const g of guards(n)) for (const r of readsIn(g)) unit.edges.push([R(r), d.key]);
          } else if (unit.imports.has(own(id.text))) {
            const p = id.parent, imp = unit.imports.get(own(id.text));
            unit.xwrites.push([own(id.text), imp.name === "*" && p && ts.isPropertyAccessExpression(p) && p.expression === id ? p.name.text : null, lineFix(n), false]);
          }
        }
        ts.forEachChild(n, (c) => hw(c, depth));
      };
      // Vue runs a handler written as statements when the event fires
      hw(e, f.inline ? 1 : 0);
      if (/^on:?key(down|up|press)$/.test(f.name || "")) keyHandlers.push([e, root, fsf, base]);
    }
  }

  // keys: comparisons in each key handler (and the functions of this file it calls)
  const seen = new Set();
  const keysIn = (body, sfx, base, depth, evt = null, evtNode = null) => {
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
    // the key an event carries: e.key, event.code, a `key` destructured from it
    const aliases = new Set();
    const bindKeys = (b) => {
      if (b && ts.isObjectBindingPattern(b))
        for (const el of b.elements) if (ts.isIdentifier(el.name) && KEY_PROPS.has((el.propertyName || el.name).text)) aliases.add(el.name.text);
    };
    if (evtNode) bindKeys(evtNode);
    const findBinds = (x) => {
      if (isFn(x) && x !== body) return;
      if (ts.isVariableDeclaration(x) && x.initializer && ts.isIdentifier(strip(x.initializer)) && strip(x.initializer).text === evt) bindKeys(x.name);
      ts.forEachChild(x, findBinds);
    };
    findBinds(body);
    const EVENT = /^(e|ev|evt|event|\$event|ke|keyEvent|keyboardEvent)$/;
    const keyProp = (x) => {
      x = strip(x);
      while (x && ts.isCallExpression(x) && ts.isPropertyAccessExpression(x.expression) && /^to(Lower|Upper)Case$/.test(x.expression.name.text)) x = strip(x.expression.expression);
      if (x && ts.isIdentifier(x)) return aliases.has(x.text) && !(x.parent && ts.isBindingElement(x.parent));
      if (!x || !ts.isPropertyAccessExpression(x) || !KEY_PROPS.has(x.name.text)) return false;
      const r = rootName(x.expression);
      return !!r && (r.text === evt || EVENT.test(r.text) || r.text === "window");
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
    const EQ = [ts.SyntaxKind.EqualsEqualsEqualsToken, ts.SyntaxKind.EqualsEqualsToken];
    const NE = [ts.SyntaxKind.ExclamationEqualsEqualsToken, ts.SyntaxKind.ExclamationEqualsToken];
    const gap = (at, why) => {
      for (let f = at; f; f = f.parent) {
        const name = isFn(f) && f.name ? f.name.getText(sfx) : f.parent && isFn(f) && ts.isVariableDeclaration(f.parent) && ts.isIdentifier(f.parent.name) ? f.parent.name.text : null;
        if (name && HOTKEY_API.test(name)) return;
      }
      unit.unresolved.push({ line: lineOf(sfx, at, base), why });
    };
    // a literal, or a const naming one (in this file)
    const value = (x) => {
      x = strip(x);
      const v0 = lit(x);
      if (v0 !== null || !ts.isIdentifier(x)) return v0;
      const c = constInit(x.text);
      return c ? lit(c) : null;
    };
    const table = (x) => {
      x = strip(x);
      const c = ts.isIdentifier(x) ? constInit(x.text) : x;
      return c ? strip(c) : null;
    };
    // `if (e.key !== 'Enter') return`: the other keys do nothing
    const exits = (n) => {
      const p = n.parent;
      if (!p || !ts.isIfStatement(p) || p.expression !== n || p.elseStatement) return false;
      const t = p.thenStatement;
      const quiet = (x) => ts.isReturnStatement(x) || ts.isBreakStatement(x) || ts.isContinueStatement(x);
      return quiet(t) || (ts.isBlock(t) && t.statements.length === 1 && quiet(t.statements[0]));
    };
    const guarded = (n) => guards(n).some((g) => {
      let hit = false;
      const f = (x) => {
        if (hit || isFn(x)) return;
        if (ts.isBinaryExpression(x) && EQ.includes(x.operatorToken.kind) && ((keyProp(x.left) && value(x.right) !== null) || (keyProp(x.right) && value(x.left) !== null))) hit = true;
        else if (ts.isCallExpression(x) && ts.isPropertyAccessExpression(x.expression) && x.expression.name.text === "includes" && x.arguments[0] && keyProp(x.arguments[0])) hit = true;
        else ts.forEachChild(x, f);
      };
      f(g);
      return hit;
    });
    const use = (k) => {
      // k: the key as read (e.key, e.key.toLowerCase()); what the handler does with it
      let x = k;
      while (x.parent && (ts.isParenthesizedExpression(x.parent) || ts.isAsExpression(x.parent) || ts.isNonNullExpression(x.parent) || (ts.isPropertyAccessExpression(x.parent) && /^to(Lower|Upper)Case$/.test(x.parent.name.text) && x.parent.parent && ts.isCallExpression(x.parent.parent) && (x = x.parent)))) x = x.parent;
      const p = x.parent;
      if (!p) return;
      if (ts.isBinaryExpression(p) && (EQ.includes(p.operatorToken.kind) || NE.includes(p.operatorToken.kind))) {
        const other = p.left === x ? p.right : p.left;
        const val = value(other);
        if (val === null) return gap(p, "compares the key with a value it computes");
        add(val, p);
        if (NE.includes(p.operatorToken.kind) && !exits(p)) gap(p, "acts on every key but one");
        return;
      }
      if (ts.isSwitchStatement(p) && p.expression === x) {
        for (const c of p.caseBlock.clauses) {
          if (ts.isCaseClause(c)) {
            const val = value(c.expression);
            if (val === null) gap(c, "a case the source does not spell out");
            else add(val, c);
          } else if (c.statements.some((st) => !ts.isBreakStatement(st) && !ts.isReturnStatement(st))) gap(c, "acts on the keys no case names");
        }
        return;
      }
      if (ts.isCallExpression(p) && p.arguments.includes(x) && ts.isPropertyAccessExpression(p.expression)) {
        const m = p.expression.name.text;
        const t = table(p.expression.expression);
        if (m === "includes" && t && ts.isArrayLiteralExpression(t)) {
          for (const e of t.elements) value(e) === null ? gap(e, "a key the source does not spell out") : add(value(e), p);
          return;
        }
        if ((m === "get" || m === "has") && t && ts.isNewExpression(t) && t.arguments && t.arguments[0] && ts.isArrayLiteralExpression(strip(t.arguments[0]))) {
          for (const e of strip(t.arguments[0]).elements) {
            const pair = strip(e);
            const val = pair && ts.isArrayLiteralExpression(pair) && pair.elements[0] ? value(pair.elements[0]) : null;
            val === null ? gap(e, "a key the source does not spell out") : add(val, p);
          }
          return;
        }
      }
      if (ts.isElementAccessExpression(p) && p.argumentExpression === x) {
        const t = table(p.expression);
        if (t && ts.isObjectLiteralExpression(t)) {
          for (const q of t.properties) {
            const name = q.name && (ts.isIdentifier(q.name) || ts.isStringLiteralLike(q.name) || ts.isNumericLiteral(q.name)) ? q.name.text : null;
            name === null ? gap(q, "a key the source does not spell out") : add(name, p);
          }
          return;
        }
        return gap(p, "looks the key up in a table the source does not spell out");
      }
      if (guarded(p)) return;
      gap(p, "passes the key on");
    };
    const v = (n) => {
      if (keyProp(n) && (ts.isPropertyAccessExpression(strip(n)) || ts.isIdentifier(strip(n)))) {
        use(n);
        return;
      }
      if (ts.isCallExpression(n) && ts.isIdentifier(n.expression) && fnDecls.has(n.expression.text)) {
        const f = fnDecls.get(n.expression.text);
        if (f.getSourceFile() === sf) keysIn(f.body, sf, 0, depth + 1, param(f), f.parameters && f.parameters[0] && f.parameters[0].name);
      } else if (ts.isCallExpression(n) && evt && n.arguments.some((a) => ts.isIdentifier(strip(a)) && strip(a).text === evt)) gap(n, "hands the event to code in another file");
      ts.forEachChild(n, v);
    };
    v(body);
  };
  function param(f) {
    return f.parameters && f.parameters[0] && ts.isIdentifier(f.parameters[0].name) ? f.parameters[0].name.text : null;
  }
  // a const's initializer, when the name is declared once in this file
  const constInit = (name) => {
    let found = null, n = 0;
    for (const sc of [root, ...scopes.values()]) {
      const d = sc.decls.get(name);
      if (!d) continue;
      n++;
      const list = d.node && d.node.parent;
      if (d.kind !== "param" && d.init && list && (list.flags & ts.NodeFlags.Const) !== 0) found = d.init;
    }
    return n === 1 ? found : null;
  };
  const first = (f) => f.parameters && f.parameters[0] && f.parameters[0].name;
  for (const [h0, scope, fsf, base] of keyHandlers) {
    const h = strip(h0);
    if (isFn(h)) keysIn(h.body, fsf || sf, base || 0, 0, param(h), first(h));
    else if (ts.isSourceFile(h)) keysIn(h, fsf, base || 0, 0, "$event");
    else if (ts.isIdentifier(h)) {
      const [, d] = scope.lookup(h.text);
      const f = d && (d.kind === "function" ? d.node : d.init && isFn(d.init) ? d.init : null);
      if (f) keysIn(f.body, sf, 0, 0, param(f), first(f));
      else unit.unresolved.push({ line: lineOf(fsf || sf, h, base || 0), why: `its key handler ${h.text} is not in this file` });
    } else unit.unresolved.push({ line: lineOf(fsf || sf, h, base || 0), why: "a key handler the source does not spell out" });
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
    fragments = svelte ? svelteExprs(parts.markup) : vueExprs(parts.markup);
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
  unit.sf = sf;
  return unit;
}

// A module an import names, among the files scanned.
function resolve(units, from, spec) {
  if (!spec.startsWith(".")) return null;
  const parts = from.split("/").slice(0, -1);
  for (const seg of spec.split("/")) {
    if (seg === "..") parts.pop();
    else if (seg !== ".") parts.push(seg);
  }
  const base = parts.join("/");
  for (const ext of ["", ".ts", ".js", ".tsx", ".jsx", ".mjs", ".svelte.ts", ".svelte.js", ".svelte", ".vue", "/index.ts", "/index.js"]) if (units.has(base + ext)) return base + ext;
  return null;
}

// What decides rendering and everything that flows into it, across the
// files: a variable qualified by its module, an import by what it names.
function state(units) {
  const q = (u, name) => {
    const imp = !name.includes("@") && u.imports.get(name);
    if (!imp) return `${u.path}#${name}`;
    const t = resolve(units, u.path, imp.from);
    if (!t) return `${imp.from}#${imp.name}`;
    return imp.name === "*" ? `${t}#*` : `${t}#${units.get(t).exports.get(imp.name) || imp.name}`;
  };
  const influence = new Set();
  const content = new Set();
  const edges = [];
  const xw = new Map(); // qualified -> {writes, clock}
  for (const u of units.values()) {
    for (const r of u.render) influence.add(q(u, r));
    for (const r of u.content) content.add(q(u, r));
    for (const [a, b] of u.edges) edges.push([q(u, a), q(u, b)]);
    for (const [local, prop, line, timed] of u.xwrites) {
      const imp = u.imports.get(local);
      const t = resolve(units, u.path, imp.from);
      if (!t) continue;
      const name = imp.name === "*" ? prop && (units.get(t).exports.get(prop) || prop) : units.get(t).exports.get(imp.name) || imp.name;
      if (!name) continue;
      const k = `${t}#${name}`;
      if (!xw.has(k)) xw.set(k, { writes: [], clock: [] });
      xw.get(k)[timed ? "clock" : "writes"].push(`${u.path}:${line}`);
    }
  }
  const close = (set) => {
    // a namespace import read where rendering is decided reads every export
    for (const k of [...set]) if (k.endsWith("#*") && units.has(k.slice(0, -2))) for (const [, local] of units.get(k.slice(0, -2)).exports) set.add(`${k.slice(0, -2)}#${local}`);
    let grew = true;
    while (grew) {
      grew = false;
      for (const [a, b] of edges)
        if (set.has(b) && !set.has(a)) {
          set.add(a);
          grew = true;
        }
    }
  };
  close(influence);
  close(content);
  const out = [];
  for (const u of units.values()) {
    const sf = u.sf;
    const names = new Map();
    for (const [, d] of u.state) names.set(d.name, (names.get(d.name) || 0) + 1);
    for (const [s, d] of u.state) {
      const k = `${u.path}#${d.key}`;
      const x = xw.get(k) || { writes: [], clock: [] };
      const w = [...(u.writes.get(d) || []), ...x.writes];
      if (!w.length || !(influence.has(k) || content.has(k))) continue;
      const reads = u.reads.get(d.name) || [];
      let component = null;
      for (let n = s.node; n && n !== sf; n = n.parent) {
        if (isFn(n) && n.name) {
          component = n.name.getText(sf);
          break;
        }
        if (ts.isVariableDeclaration(n) && ts.isIdentifier(n.name)) {
          component = n.name.text;
          break;
        }
      }
      const clock = [...(u.clock.get(d) || []), ...x.clock];
      const lines = (xs) => [...new Set(xs)].sort((a, b) => (typeof a === typeof b ? (a < b ? -1 : a > b) : typeof a === "number" ? -1 : 1)).slice(0, 3);
      out.push({ name: d.name, path: u.path, line: d.line, clock: lines(clock), writes: lines(w), reads: lines(reads), component, react: !!d.react, affects: [...(influence.has(k) ? ["structure"] : []), ...(content.has(k) ? ["content"] : [])], unique: names.get(d.name) === 1 && u.declared.get(d.name) === 1 });
    }
  }
  return out;
}

const input = JSON.parse(fs.readFileSync(0, "utf8"));
const out = { keys: [], state: [], storage: [], unresolved: [], errors: [] };
const units = new Map();
for (const f of input.files) {
  try {
    const u = scanFile(f.path, f.text);
    units.set(f.path, u);
    out.keys.push(...u.keys);
    out.storage.push(...u.storage.map((x) => ({ ...x, path: f.path })));
    out.unresolved.push(...u.unresolved.map((x) => ({ ...x, path: f.path })));
  } catch (e) {
    out.errors.push(`${f.path}: ${String(e && e.message || e).split("\n")[0]}`);
  }
}
out.state = state(units);
process.stdout.write(JSON.stringify(out));
