// TypeScript -> telic IR (JSON).
//
// Usage: node lower.mjs <root> <file.ts>...   (prints one JSON document)
//
// Semantics are JavaScript's, stated explicitly:
//   * `number` is an exact rational unless integrality is known. A value is an
//     integer when the code guarantees it: integer literals, `.length`,
//     Math.floor/ceil/trunc/round, int +,-,*,%, and parameters whose
//     contract says `Number.isInteger(p)` (or whose type is an alias named
//     `int`). Integrality of locals/returns is the greatest fixpoint of
//     "every assignment is integer-valued".
//   * `/` is real division; `%` truncates (sign of the dividend).
//   * reading `xs[i]` out of bounds yields `undefined` -- telic treats it as
//     an error and requires 0 <= i < xs.length.
// Anything outside the modelled subset is reported as unsupported, with a line.

import { createRequire } from "node:module";
import fs from "node:fs";
import path from "node:path";

const require = createRequire(import.meta.url);
const ts = require("typescript");

// ---------------------------------------------------------------------------
// Types

const INT = { k: "int" }, REAL = { k: "real" }, BOOL = { k: "bool" }, STR = { k: "str" }, NONE = { k: "none" };
const listOf = (elem) => ({ k: "list", elem });
const optionOf = (inner) => (inner.k === "option" || inner.k === "opaque" ? inner : inner.k === "list" || inner.k === "dict" ? opaque("optional container") : { k: "option", inner });
const opaque = (why = "") => ({ k: "opaque", why });
const classOf = (name) => ({ k: "class", name });
const tyKey = (t) => (t.k === "opaque" ? "opaque" : t.k === "dict" ? `dict<${tyKey(t.key)},${tyKey(t.val)}>` : t.k === "option" ? `option<${tyKey(t.inner)}>` : t.k === "list" ? `list<${tyKey(t.elem)}>` : t.k === "enum" || t.k === "class" || t.k === "record" ? `${t.k}:${t.name}` : t.k);
const tyEq = (a, b) => tyKey(a) === tyKey(b);
const isNum = (t) => t && (t.k === "int" || t.k === "real");
const hasOpaque = (t) => t.k === "opaque" || (t.k === "list" && hasOpaque(t.elem)) || (t.k === "option" && hasOpaque(t.inner)) || (t.k === "dict" && (hasOpaque(t.key) || hasOpaque(t.val)));
const tyStr = (t) => (t.k === "list" ? `${tyStr(t.elem)}[]` : t.k === "record" || t.k === "class" || t.k === "enum" ? t.name : t.k === "real" ? "number" : t.k === "int" ? "int" : t.k === "option" ? `${tyStr(t.inner)} | undefined` : t.k === "dict" ? `Map<${tyStr(t.key)}, ${tyStr(t.val)}>` : t.k);
const GLOBALS = new Set(["Date", "JSON", "Math", "Number", "String", "Object", "Array", "Promise", "fetch", "console", "process", "window", "document", "crypto", "setTimeout", "clearTimeout", "setInterval", "parseInt", "parseFloat", "isNaN", "isFinite", "Symbol", "BigInt", "Error", "Intl", "URL", "URLSearchParams", "localStorage", "sessionStorage", "navigator", "location", "globalThis", "undefined", "NaN", "Infinity", "structuredClone", "encodeURIComponent", "decodeURIComponent", "require", "module", "exports", "__dirname", "__filename", "Buffer", "Set", "WeakMap", "WeakSet", "Reflect", "Proxy", "queueMicrotask", "alert", "performance"]);

class LowerError extends Error {
  constructor(msg, line) {
    super(msg);
    this.line = line;
  }
}

// ---------------------------------------------------------------------------
// Contract comments (mirrors telic/contracts.py)

const CLAUSE_KW = new Set(["requires", "ensures", "invariant", "decreases", "assert", "assume", "raises"]);
const DIRECTIVE_KW = new Set(["intent", "index", "mirrors", "trusted", "pure"]);
const FUNCTION_KW = new Set(["requires", "ensures", "decreases", "raises", "intent", "mirrors", "trusted", "pure"]);
const LOOP_KW = new Set(["invariant", "decreases", "index"]);
const STMT_KW = new Set(["assert", "assume"]);
const INTENT_ID = "[A-Z][A-Z0-9]*(?:-[A-Z0-9]+)*";
const TAG_RE = new RegExp(`^\\[\\s*(${INTENT_ID}(?:\\s*,\\s*${INTENT_ID})*)\\s*\\]\\s*`);
const INTENT_DECL_RE = new RegExp(`^(${INTENT_ID})\\s*(?::\\s*(.*))?$`);
const INTENT_LIST_RE = new RegExp(`^${INTENT_ID}(?:\\s*,\\s*${INTENT_ID})*$`);

// Every comment in the file, via the compiler's own trivia ranges (a raw
// scanner can mistake `//` inside a template literal or regex for a comment).
function collectComments(sf) {
  const seen = new Map();
  const text = sf.text;
  const grab = (ranges) => {
    for (const r of ranges || []) {
      if (r.kind !== ts.SyntaxKind.SingleLineCommentTrivia || seen.has(r.pos)) continue;
      const lc = sf.getLineAndCharacterOfPosition(r.pos);
      seen.set(r.pos, { line: lc.line + 1, col: lc.character, text: text.slice(r.pos, r.end), pos: r.pos });
    }
  };
  const walk = (node) => {
    grab(ts.getLeadingCommentRanges(text, node.getFullStart()));
    grab(ts.getTrailingCommentRanges(text, node.getEnd()));
    for (const child of node.getChildren(sf)) walk(child);
  };
  walk(sf);
  return [...seen.values()].sort((a, b) => a.pos - b.pos);
}

function parseContractLines(comments) {
  const out = [];
  for (const c of comments) {
    if (!c.text.startsWith("//@")) continue;
    const body = c.text.slice(3);
    let stripped = body.trim();
    if (!stripped) continue;
    const lead = body.length - body.trimStart().length;
    let baseCol = c.col + 3 + lead;
    let tags = [];
    const m = TAG_RE.exec(stripped);
    if (m) {
      tags = m[1].split(",").map((s) => s.trim());
      baseCol += m[0].length;
      stripped = stripped.slice(m[0].length);
    }
    const word = stripped.split(/\s+/)[0] || "";
    if (CLAUSE_KW.has(word) || DIRECTIVE_KW.has(word)) {
      const rest = stripped.slice(word.length);
      const pl = rest.length - rest.trimStart().length;
      out.push({ keyword: word, payload: rest.trim(), line: c.line, col: c.col, pos: c.pos, payloadCol: baseCol + word.length + pl, tags, endLine: c.line, rawLines: [c.line], consumed: false });
    } else if (out.length && out[out.length - 1].endLine === c.line - 1 && !tags.length) {
      const prev = out[out.length - 1];
      prev.payload += "\n" + stripped;
      prev.endLine = c.line;
      prev.rawLines.push(c.line);
    } else {
      throw new LowerError(`unknown contract keyword '${word}'`, c.line);
    }
  }
  return out;
}

function parseIntent(cl) {
  const payload = cl.payload.split(/\s+/).join(" ");
  const m = INTENT_DECL_RE.exec(payload);
  if (m && m[2] !== undefined) return { ids: [m[1]], text: m[2].trim() };
  if (INTENT_LIST_RE.test(payload)) return { ids: payload.split(",").map((s) => s.trim()), text: null };
  throw new LowerError("malformed intent: write '@intent ID: sentence' to declare or '@intent ID' to link", cl.line);
}

// ---------------------------------------------------------------------------

const JS_ASSUMPTIONS = [
  "number is modelled as an exact rational (no NaN, Infinity, or rounding error)",
  "integer-valued numbers stay within the safe range ±2^53",
  "distinct array arguments do not alias each other",
  "console.* calls have no effect on program state",
];

class ModuleLowerer {
  constructor(file, rel, sf) {
    this.file = file;
    this.rel = rel;
    this.sf = sf;
    this.src = sf.text;
    this.lines = sf.text.split(/\r?\n/);
    this.module = { path: rel, language: "typescript", source: sf.text, functions: [], intents: [], records: {}, classes: {}, imports: {}, problems: [], notes: [], assumptions: JS_ASSUMPTIONS };
    this.aliases = {};
    this.sigs = {}; // name -> {params, ret, node}
    this.classes = {}; // name -> {node, fields: [[n, ty]], props, setters, statics, home: ModuleLowerer}
    this.enums = {}; // name -> enum type
    this.namespaces = {}; // `import * as ns` of a checked module -> ModuleLowerer
    this.imported = {}; // local -> {mod, name}
    this.importDecls = [];
    this.constants = {}; // module-level `const X = <literal>`
    this.globalsBound = new Set(); // module-level names that are not modelled
  }

  run() {
    for (const _ of this.phases()) {
      /* single module */
    }
    return this.module;
  }

  line(node) {
    return this.sf.getLineAndCharacterOfPosition(node.getStart(this.sf)).line + 1;
  }
  loc(node) {
    const s = this.sf.getLineAndCharacterOfPosition(node.getStart(this.sf));
    const e = this.sf.getLineAndCharacterOfPosition(node.getEnd());
    return [s.line + 1, s.character, e.line === s.line ? e.character : 0];
  }

  // Lowering in three phases so a project can link imports between them:
  // yields "names" once records, enums and class names are known, and
  // "signatures" once fields and signatures are.
  *phases() {
    try {
      this.contracts = parseContractLines(collectComments(this.sf));
    } catch (e) {
      this.module.problems.push([e.message, e.line || 0]);
      return;
    }
    const isGen = (n) => !!n.asteriskToken;
    for (const st of this.sf.statements) {
      if (ts.isImportDeclaration(st) && ts.isStringLiteral(st.moduleSpecifier)) {
        const spec = st.moduleSpecifier.text;
        const cl = st.importClause;
        if (!cl) continue;
        if (cl.name) this.importDecls.push({ spec, local: cl.name.text, name: "default" });
        const nb = cl.namedBindings;
        if (nb && ts.isNamespaceImport(nb)) this.importDecls.push({ spec, local: nb.name.text, name: "*" });
        else if (nb && ts.isNamedImports(nb)) for (const el of nb.elements) this.importDecls.push({ spec, local: el.name.text, name: (el.propertyName || el.name).text });
        for (const d of this.importDecls) this.globalsBound.add(d.local);
      } else if (ts.isVariableStatement(st)) {
        for (const d of st.declarationList.declarations) {
          if (!ts.isIdentifier(d.name)) continue;
          const init = d.initializer;
          const lit = init && (ts.isNumericLiteral(init) || ts.isStringLiteral(init) || init.kind === ts.SyntaxKind.TrueKeyword || init.kind === ts.SyntaxKind.FalseKeyword || (ts.isPrefixUnaryExpression(init) && init.operator === ts.SyntaxKind.MinusToken && ts.isNumericLiteral(init.operand)));
          if (lit && st.declarationList.flags & ts.NodeFlags.Const) this.constants[d.name.text] = init;
          else if (!(init && (ts.isArrowFunction(init) || ts.isFunctionExpression(init)))) this.globalsBound.add(d.name.text);
        }
      }
    }
    // Records, aliases, enums, classes.
    for (const st of this.sf.statements) {
      if (ts.isEnumDeclaration(st)) this.enumDecl(st);
    }
    for (const st of this.sf.statements) {
      if (ts.isClassDeclaration(st) && st.name) {
        const ext = st.heritageClauses && st.heritageClauses.find((h) => h.token === ts.SyntaxKind.ExtendsKeyword);
        if (ext) {
          this.globalsBound.add(st.name.text);
          const base = ext.types[0] ? ext.types[0].expression.getText(this.sf) : "?";
          // an Error subclass is only ever thrown; other subclasses are library-like values
          if (!/(Error|Exception)$/.test(base)) this.module.notes.push([`class ${st.name.text}: subclass of ${base}; inheritance is not modelled for TypeScript yet, so its instances are treated as library values`, this.line(st)]);
          continue;
        }
        this.classes[st.name.text] = { node: st, fields: [], props: new Set(), setters: new Set(), statics: new Set(), home: this };
      }
    }
    for (const st of this.sf.statements) {
      if (ts.isInterfaceDeclaration(st)) this.record(st.name.text, st.members, st);
      else if (ts.isTypeAliasDeclaration(st)) {
        if (ts.isTypeLiteralNode(st.type) && !st.type.members.some((m) => ts.isIndexSignatureDeclaration(m))) this.record(st.name.text, st.type.members, st);
        else this.aliases[st.name.text] = st.type;
      }
    }
    yield "names";
    // Class fields.
    for (const [name, c] of Object.entries(this.classes)) {
      if (c.home !== this) continue;
      try {
        this.classFields(name, c);
      } catch (e) {
        if (!(e instanceof LowerError)) throw e;
        this.module.problems.push([`class ${name}: ${e.message}`, e.line || this.line(c.node)]);
        delete this.classes[name];
      }
    }
    // Function declarations (and `const f = (...) => ...`), methods.
    const fns = [];
    for (const st of this.sf.statements) {
      if (ts.isFunctionDeclaration(st) && isGen(st)) continue;
      if (ts.isFunctionDeclaration(st) && st.name && st.body) fns.push({ name: st.name.text, node: st, exported: !!(ts.getCombinedModifierFlags(st) & ts.ModifierFlags.Export) });
      else if (ts.isVariableStatement(st) && st.declarationList.declarations.length === 1) {
        const d = st.declarationList.declarations[0];
        if (ts.isIdentifier(d.name) && d.initializer && (ts.isArrowFunction(d.initializer) || ts.isFunctionExpression(d.initializer)) && st.declarationList.flags & ts.NodeFlags.Const && !isGen(d.initializer)) {
          fns.push({ name: d.name.text, node: d.initializer, stmt: st, exported: !!(ts.getCombinedModifierFlags(st) & ts.ModifierFlags.Export) });
        }
      }
    }
    for (const [cname, c] of Object.entries(this.classes)) {
      if (c.home !== this) continue;
      let ctor = null;
      for (const m of c.node.members) {
        const isStatic = !!(m.modifiers && m.modifiers.some((x) => x.kind === ts.SyntaxKind.StaticKeyword));
        if (ts.isConstructorDeclaration(m) && m.body) ctor = m;
        else if (ts.isMethodDeclaration(m) && m.body && ts.isIdentifier(m.name) && !m.asteriskToken) {
          if (isStatic) c.statics.add(`${cname}.${m.name.text}`);
          fns.push({ name: `${cname}.${m.name.text}`, node: m, cls: cname, isStatic, exported: true });
        } else if (ts.isGetAccessorDeclaration(m) && m.body && ts.isIdentifier(m.name)) {
          c.props.add(`${cname}.${m.name.text}`);
          fns.push({ name: `${cname}.${m.name.text}`, node: m, cls: cname, exported: true });
        } else if (ts.isSetAccessorDeclaration(m) && m.body && ts.isIdentifier(m.name)) {
          c.setters.add(`${cname}.${m.name.text}`);
          fns.push({ name: `${cname}.${m.name.text}.setter`, node: m, cls: cname, exported: true });
        }
      }
      fns.push({ name: `${cname}.__init__`, node: ctor, cls: cname, ctor: true, classNode: c.node, exported: true });
    }
    for (const f of fns) {
      try {
        this.sigs[f.name] = this.signature(f);
      } catch (e) {
        if (!(e instanceof LowerError)) throw e;
        this.module.problems.push([`${f.name}: ${e.message}`, e.line || this.line(f.node || f.classNode)]);
      }
    }
    this.inferIntegrality(fns.filter((f) => !f.ctor));
    yield "signatures";
    for (const [cname, c] of Object.entries(this.classes)) {
      if (c.home !== this) continue;
      this.module.classes[cname] = { fields: c.fields, invariants: this.classInvariants(cname, c), loc: this.loc(c.node) };
    }
    for (const f of fns) {
      if (!this.sigs[f.name]) continue;
      const fl = new FunctionLowerer(this, f);
      this.module.functions.push(fl.lower());
    }
    for (const cl of this.contracts) {
      if (cl.consumed) continue;
      if (cl.keyword === "intent") {
        cl.consumed = true;
        try {
          const { ids, text } = parseIntent(cl);
          if (text === null) this.module.problems.push(["'@intent ID' outside a function links nothing; declare with '@intent ID: sentence'", cl.line]);
          else this.module.intents.push({ id: ids[0], text, line: cl.line, col: cl.col });
        } catch (e) {
          this.module.problems.push([e.message, cl.line]);
        }
      }
    }
    const spans = [];
    const visit = (n) => {
      if ((ts.isClassDeclaration(n) || ts.isClassExpression(n)) && !(n.name && this.classes[n.name.text])) {
        const name = n.name ? n.name.text : "class";
        spans.push([n.getStart(this.sf), n.getEnd(), `class '${name}' is not checked (see the problem reported for it)`]);
      }
      ts.forEachChild(n, visit);
    };
    visit(this.sf);
    const reported = new Set();
    for (const cl of this.contracts) {
      if (cl.consumed) continue;
      const span = spans.find(([a, b]) => cl.pos >= a && cl.pos <= b);
      if (span) {
        if (!reported.has(span[2])) this.module.problems.push([span[2], cl.line]);
        reported.add(span[2]);
        continue;
      }
      this.module.problems.push([`stray '@${cl.keyword}' is not attached to any function, loop, or statement`, cl.line]);
    }
  }

  enumDecl(st) {
    const members = [], values = [];
    let next = 0;
    for (const m of st.members) {
      const name = m.name.getText(this.sf).replace(/^["']|["']$/g, "");
      let v = next;
      if (m.initializer) {
        if (ts.isNumericLiteral(m.initializer)) v = Number(m.initializer.text);
        else if (ts.isStringLiteral(m.initializer)) v = m.initializer.text;
        else v = null;
      }
      members.push(name);
      values.push(v);
      next = typeof v === "number" ? v + 1 : next;
    }
    this.enums[st.name.text] = { k: "enum", name: st.name.text, members, values };
  }

  classFields(cname, c) {
    const known = new Set();
    const add = (n, t) => {
      if (known.has(n)) return;
      known.add(n);
      c.fields.push([n, t]);
    };
    const litType = (init) => {
      if (!init) return null;
      if (ts.isNumericLiteral(init)) return /^\d+$/.test(init.text) ? REAL : REAL;
      if (ts.isStringLiteral(init) || ts.isNoSubstitutionTemplateLiteral(init)) return STR;
      if (init.kind === ts.SyntaxKind.TrueKeyword || init.kind === ts.SyntaxKind.FalseKeyword) return BOOL;
      if (ts.isPropertyAccessExpression(init) && ts.isIdentifier(init.expression) && this.enums[init.expression.text]) return this.enums[init.expression.text];
      return null;
    };
    for (const m of c.node.members) {
      if (ts.isPropertyDeclaration(m) && ts.isIdentifier(m.name) && !(m.modifiers && m.modifiers.some((x) => x.kind === ts.SyntaxKind.StaticKeyword))) {
        let t = m.type ? this.typeOf(m.type) : litType(m.initializer) || opaque(`field ${m.name.text}`);
        if (m.questionToken) t = optionOf(t);
        add(m.name.text, t);
      }
      if (ts.isConstructorDeclaration(m)) {
        for (const p of m.parameters) {
          const isProp = p.modifiers && p.modifiers.some((x) => [ts.SyntaxKind.PublicKeyword, ts.SyntaxKind.PrivateKeyword, ts.SyntaxKind.ProtectedKeyword, ts.SyntaxKind.ReadonlyKeyword].includes(x.kind));
          if (isProp && ts.isIdentifier(p.name)) add(p.name.text, p.type ? this.typeOf(p.type) : opaque("unannotated"));
        }
      }
    }
    // `this.x = ...` anywhere in the class: a field
    const visit = (n) => {
      if (ts.isBinaryExpression(n) && n.operatorToken.kind === ts.SyntaxKind.EqualsToken && ts.isPropertyAccessExpression(n.left) && n.left.expression.kind === ts.SyntaxKind.ThisKeyword) {
        const name = n.left.name.text;
        if (!known.has(name) && !c.props.has(`${cname}.${name}`)) {
          const fn = ts.findAncestor(n, (x) => ts.isConstructorDeclaration(x) || ts.isMethodDeclaration(x));
          let t = litType(n.right);
          if (!t && fn && ts.isIdentifier(n.right)) {
            const prm = fn.parameters.find((p) => ts.isIdentifier(p.name) && p.name.text === n.right.text);
            if (prm && prm.type) t = this.typeOf(prm.type);
          }
          add(name, t || opaque(`field ${name}`));
        }
      }
      ts.forEachChild(n, visit);
    };
    visit(c.node);
  }

  classInvariants(cname, c) {
    const out = [];
    const start = c.node.getStart(this.sf), end = c.node.getEnd();
    const inMember = (pos) => c.node.members.some((m) => (ts.isMethodDeclaration(m) || ts.isConstructorDeclaration(m) || ts.isGetAccessorDeclaration(m) || ts.isSetAccessorDeclaration(m)) && m.body && pos > m.body.getStart(this.sf) && pos < m.body.getEnd());
    for (const cl of this.contracts) {
      if (cl.consumed || cl.keyword !== "invariant" || cl.pos < start || cl.pos > end || inMember(cl.pos)) continue;
      cl.consumed = true;
      try {
        const fl = new FunctionLowerer(this, { name: `${cname}.<invariant>`, node: null, cls: cname, invariantScope: true });
        const cls = fl.clause(cl, "invariant", cl.tags);
        const walk = (x) => {
          if (!x || typeof x !== "object") return;
          if (x.e === "Field" && x.obj.ty.k === "class" && !(x.obj.e === "Var" && x.obj.name === "self")) throw new LowerError("a class invariant may only read fields of 'this', not of other objects", cl.line);
          if (x.e === "Call" && x.args.some((a) => a.ty.k === "class")) throw new LowerError("a class invariant may not call methods; write the condition on this's fields", cl.line);
          for (const v of Object.values(x)) if (Array.isArray(v)) v.forEach(walk);
          else if (v && typeof v === "object") walk(v);
        };
        walk(cls.expr);
        out.push(cls);
      } catch (e) {
        if (!(e instanceof LowerError)) throw e;
        this.module.problems.push([`class ${cname}: invariant: ${e.message}`, e.line || cl.line]);
      }
    }
    return out;
  }

  record(name, members, node) {
    const fields = [];
    for (const m of members) {
      if (!ts.isPropertySignature(m) || !m.type || !ts.isIdentifier(m.name)) return;
      let t;
      try {
        t = this.typeOf(m.type);
      } catch {
        return;
      }
      if (m.questionToken) t = optionOf(t);
      if (t.k === "list" || t.k === "dict" || t.k === "opaque" || t.k === "class") return;
      fields.push([m.name.text, t]);
    }
    this.module.records[name] = { k: "record", name, fields };
  }

  typeOf(tn, intHint = false, depth = 0) {
    if (!tn) throw new LowerError("missing type annotation");
    if (depth > 20) return opaque("recursive type");
    const K = ts.SyntaxKind;
    switch (tn.kind) {
      case K.NumberKeyword:
        return intHint ? INT : REAL;
      case K.BooleanKeyword:
        return BOOL;
      case K.StringKeyword:
        return STR;
      case K.VoidKeyword:
      case K.UndefinedKeyword:
      case K.NullKeyword:
        return NONE;
      case K.AnyKeyword:
      case K.UnknownKeyword:
      case K.ObjectKeyword:
      case K.NeverKeyword:
      case K.BigIntKeyword:
      case K.SymbolKeyword:
        return opaque(tn.getText(this.sf));
    }
    if (ts.isLiteralTypeNode(tn) && tn.literal.kind === K.NullKeyword) return NONE;
    if (ts.isArrayTypeNode(tn)) {
      const e = this.typeOf(tn.elementType, false, depth + 1);
      return e.k === "list" || e.k === "dict" ? opaque(tn.getText(this.sf)) : listOf(e);
    }
    if (ts.isTypeOperatorNode(tn) && tn.operator === K.ReadonlyKeyword) return this.typeOf(tn.type, intHint, depth + 1);
    if (ts.isTypeReferenceNode(tn) && ts.isIdentifier(tn.typeName)) {
      const n = tn.typeName.text;
      const targs = tn.typeArguments || [];
      if ((n === "Array" || n === "ReadonlyArray") && targs.length === 1) {
        const e = this.typeOf(targs[0], false, depth + 1);
        return e.k === "list" || e.k === "dict" ? opaque(tn.getText(this.sf)) : listOf(e);
      }
      if ((n === "Map" || n === "Record" || n === "ReadonlyMap") && targs.length === 2) {
        const k = this.typeOf(targs[0], false, depth + 1), v = this.typeOf(targs[1], false, depth + 1);
        if (!["int", "real", "str", "bool"].includes(k.k) || ["list", "dict", "option"].includes(v.k)) return opaque(tn.getText(this.sf));
        return { k: "dict", key: k, val: v, js: n === "Record" ? "object" : "map" };
      }
      if (n === "Promise" && targs.length === 1) return this.typeOf(targs[0], intHint, depth + 1);
      if (n === "Readonly" && targs.length === 1) return this.typeOf(targs[0], intHint, depth + 1);
      if (["int", "Int", "integer", "Integer"].includes(n) && this.aliases[n] && this.aliases[n].kind === K.NumberKeyword) return INT;
      if (this.module.records[n]) return this.module.records[n];
      if (this.classes[n]) return classOf(n);
      if (this.enums[n]) return this.enums[n];
      if (this.aliases[n]) return this.typeOf(this.aliases[n], intHint, depth + 1);
      return opaque(n); // a library type: unchecked
    }
    if (ts.isTypeLiteralNode(tn) && tn.members.length === 1 && ts.isIndexSignatureDeclaration(tn.members[0])) {
      const sig = tn.members[0];
      const k = this.typeOf(sig.parameters[0].type, false, depth + 1), v = this.typeOf(sig.type, false, depth + 1);
      if (["int", "real", "str"].includes(k.k) && !["list", "dict", "option"].includes(v.k)) return { k: "dict", key: k, val: v, js: "object" };
      return opaque(tn.getText(this.sf));
    }
    if (ts.isParenthesizedTypeNode(tn)) return this.typeOf(tn.type, intHint, depth + 1);
    if (ts.isUnionTypeNode(tn)) {
      if (tn.types.every((t) => ts.isLiteralTypeNode(t) && ts.isStringLiteral(t.literal))) return STR;
      const parts = tn.types.map((t) => this.typeOf(t, intHint, depth + 1));
      const rest = parts.filter((t) => t.k !== "none");
      const uniq = rest.filter((t, i) => rest.findIndex((u) => tyEq(u, t)) === i);
      let inner;
      if (uniq.length === 1) inner = uniq[0];
      else if (uniq.length > 1 && uniq.every((t) => t.k === "str")) inner = STR;
      else if (uniq.length > 1 && uniq.every(isNum)) inner = REAL;
      else return opaque(tn.getText(this.sf));
      return rest.length === parts.length ? inner : optionOf(inner);
    }
    if (ts.isLiteralTypeNode(tn) && ts.isStringLiteral(tn.literal)) return STR;
    if (ts.isLiteralTypeNode(tn) && ts.isNumericLiteral(tn.literal)) return REAL;
    return opaque(tn.getText(this.sf));
  }

  functionContracts(f) {
    // contiguous //@ lines directly above, plus lines at the start of the body
    const node = f.stmt || f.node;
    const first = this.line(node);
    const byLine = new Map();
    for (const cl of this.contracts) for (const l of cl.rawLines) byLine.set(l, cl);
    const above = [];
    for (let ln = first - 1; ln >= 1; ln--) {
      const t = this.lines[ln - 1].trim();
      if (!t.startsWith("//")) break;
      const cl = byLine.get(ln);
      if (cl && FUNCTION_KW.has(cl.keyword) && !cl.consumed && !above.includes(cl)) above.push(cl);
    }
    above.reverse();
    const body = f.node.body;
    const inside = [];
    if (body && ts.isBlock(body)) {
      const open = body.getStart(this.sf);
      const limit = body.statements.length ? body.statements[0].getStart(this.sf) : body.getEnd();
      for (const cl of this.contracts) if (cl.pos > open && cl.pos < limit && FUNCTION_KW.has(cl.keyword) && !cl.consumed) inside.push(cl);
    }
    return above.concat(inside);
  }

  signature(f) {
    const node = f.node;
    const cls = node ? this.functionContracts(f) : [];
    // integrality hints from @requires: Number.isInteger(p) / isSafeInteger(p)
    // Only a top-level conjunct `Number.isInteger(p)` makes p an integer:
    // under `!` or `||` it guarantees nothing.
    const ints = new Set();
    for (const cl of cls) {
      if (cl.keyword !== "requires") continue;
      const src = ts.createSourceFile("r.ts", "(" + cl.payload + "\n)", ts.ScriptTarget.Latest, true);
      const st = src.statements[0];
      if (!st || !ts.isExpressionStatement(st)) continue;
      const conj = (e) => {
        while (ts.isParenthesizedExpression(e)) e = e.expression;
        if (ts.isBinaryExpression(e) && e.operatorToken.kind === ts.SyntaxKind.AmpersandAmpersandToken) return conj(e.left).concat(conj(e.right));
        return [e];
      };
      for (const c of conj(st.expression)) {
        if (ts.isCallExpression(c) && c.arguments.length === 1 && ts.isIdentifier(c.arguments[0]) && ts.isPropertyAccessExpression(c.expression) && ts.isIdentifier(c.expression.expression) && c.expression.expression.text === "Number" && ["isInteger", "isSafeInteger"].includes(c.expression.name.text)) ints.add(c.arguments[0].text);
      }
    }
    const params = [];
    const defaults = {};
    let rest = null;
    if (f.cls && !f.isStatic) params.push({ name: "self", ty: classOf(f.cls) });
    const destructs = [];
    for (const p of node ? node.parameters : []) {
      let pname;
      if (!ts.isIdentifier(p.name)) {
        // ({ a, b }: Props) => ...: a parameter of the declared type, destructured on entry
        pname = `arg$${destructs.length}`;
        destructs.push([pname, p.name]);
      } else pname = p.name.text;
      if (p.dotDotDotToken) {
        params.push({ name: pname, ty: opaque("...rest") });
        rest = pname;
        continue;
      }
      let t = p.type ? this.typeOf(p.type, ints.has(pname)) : null;
      if (p.initializer) {
        const init = p.initializer;
        const lit = ts.isNumericLiteral(init) || ts.isStringLiteral(init) || init.kind === ts.SyntaxKind.TrueKeyword || init.kind === ts.SyntaxKind.FalseKeyword || (ts.isPrefixUnaryExpression(init) && ts.isNumericLiteral(init.operand));
        defaults[pname] = lit ? init : null; // null: computed at call time, unknown here
        if (!t) t = ts.isStringLiteral(init) ? STR : init.kind === ts.SyntaxKind.TrueKeyword || init.kind === ts.SyntaxKind.FalseKeyword ? BOOL : lit ? REAL : opaque("unannotated");
      }
      if (!t) t = opaque("unannotated");
      if (p.questionToken) t = optionOf(t);
      params.push({ name: pname, ty: t });
    }
    let ret = NONE;
    if (f.ctor || (node && ts.isSetAccessorDeclaration(node))) ret = NONE;
    else if (node.type) ret = this.typeOf(node.type);
    else {
      let valued = !!(node.body && !ts.isBlock(node.body));
      const visit = (n) => {
        if (n !== node && ts.isFunctionLike(n)) return;
        if (ts.isReturnStatement(n) && n.expression) valued = true;
        ts.forEachChild(n, visit);
      };
      if (node.body) visit(node.body);
      if (valued) ret = opaque("unannotated return");
    }
    return { params, ret, node, contracts: cls, intsFromContract: ints, defaults, rest, cls: f.cls, isStatic: !!f.isStatic, destructs };
  }

  // Greatest fixpoint: a number-typed function result is an int if every
  // return expression is int-valued (assuming the same of every other).
  inferIntegrality(fns) {
    const cands = fns.filter((f) => this.sigs[f.name] && this.sigs[f.name].ret.k === "real");
    for (const f of cands) this.sigs[f.name].ret = INT;
    let changed = true;
    while (changed) {
      changed = false;
      for (const f of cands) {
        const sig = this.sigs[f.name];
        if (sig.ret.k !== "int") continue;
        const fl = new FunctionLowerer(this, f, true);
        let ok = true;
        try {
          ok = fl.returnsInt();
        } catch {
          ok = false;
        }
        if (!ok) {
          sig.ret = REAL;
          changed = true;
        }
      }
    }
  }
}

// ---------------------------------------------------------------------------

class FunctionLowerer {
  constructor(ml, f, probe = false) {
    this.ml = ml;
    this.f = f;
    this.node = f.node;
    this.sig = ml.sigs[f.name] || { params: f.cls ? [{ name: "self", ty: classOf(f.cls) }] : [], ret: NONE, contracts: [], defaults: {}, rest: null, cls: f.cls };
    this.env = {};
    this.probe = probe;
    this.tmp = 0;
    this.scopes = [new Map(this.sig.params.map((p) => [p.name, p.name]))];
    this.usedIr = new Set(this.sig.params.map((p) => p.name));
    this.consts = new Set();
    this.srcNames = new Set();
    this.closures = new Map(); // local function name -> captured source names
    this.escaped = new Set();
    this.tryDepth = 0;
    const collect = (n) => {
      if (ts.isIdentifier(n)) this.srcNames.add(n.text);
      ts.forEachChild(n, collect);
    };
    if (f.node && f.node.body) collect(f.node.body);
    this.unsupported = [];
    this.intents = [];
    this.currentIntents = [];
    const anchor = f.stmt || f.node;
    if (anchor) {
      const start = anchor.getStart(ml.sf), end = f.node.getEnd();
      this.localContracts = ml.contracts.filter((cl) => cl.pos >= start && cl.pos <= end);
    } else this.localContracts = [];
  }

  selfTy() {
    return this.f.cls && !this.sig.isStatic ? classOf(this.f.cls) : null;
  }

  err(msg, node) {
    return new LowerError(msg, typeof node === "number" ? node : node ? this.ml.line(node) : 0);
  }

  // -- integrality pre-pass ---------------------------------------------

  intVars() {
    // Greatest fixpoint over local variables of type number.
    const decls = new Map(); // name -> [init/assigned expressions]
    const visit = (n) => {
      if (ts.isVariableDeclaration(n) && ts.isIdentifier(n.name)) {
        const t = n.type ? safeType(this.ml, n.type) : null;
        if ((t && t.k === "real") || (!t && n.initializer)) {
          if (!decls.has(n.name.text)) decls.set(n.name.text, []);
          if (n.initializer) decls.get(n.name.text).push(n.initializer);
        }
      } else if (ts.isBinaryExpression(n) && ts.isIdentifier(n.left)) {
        const k = n.operatorToken.kind;
        if (decls.has(n.left.text)) {
          if (k === ts.SyntaxKind.EqualsToken) decls.get(n.left.text).push(n.right);
          else if (k === ts.SyntaxKind.PlusEqualsToken || k === ts.SyntaxKind.MinusEqualsToken || k === ts.SyntaxKind.AsteriskEqualsToken || k === ts.SyntaxKind.PercentEqualsToken) decls.get(n.left.text).push(n.right);
          else if (k === ts.SyntaxKind.SlashEqualsToken) decls.get(n.left.text).push(null);
        }
      } else if (ts.isForOfStatement(n)) {
        const d = n.initializer;
        if (ts.isVariableDeclarationList(d) && d.declarations.length === 1 && ts.isIdentifier(d.declarations[0].name)) {
          const name = d.declarations[0].name.text;
          if (!decls.has(name)) decls.set(name, []);
          decls.get(name).push({ __elemOf: n.expression });
        }
      }
      ts.forEachChild(n, visit);
    };
    if (this.node && this.node.body) visit(this.node.body);
    const params = new Map(this.sig.params.map((p) => [p.name, p.ty]));
    let ints = new Set([...decls.keys()]);
    let changed = true;
    while (changed) {
      changed = false;
      for (const [name, exprs] of decls) {
        if (!ints.has(name)) continue;
        for (const e of exprs) {
          let ok;
          if (e === null) ok = false;
          else if (e.__elemOf) {
            const t = staticType(this, e.__elemOf, ints, params);
            ok = t && t.k === "list" && t.elem.k === "int";
          } else ok = isIntExpr(this, e, ints, params);
          if (!ok) {
            ints.delete(name);
            changed = true;
            break;
          }
        }
      }
    }
    return ints;
  }

  returnsInt() {
    this.intSet = this.intVars();
    const params = new Map(this.sig.params.map((p) => [p.name, p.ty]));
    const body = this.node.body;
    if (!ts.isBlock(body)) return isIntExpr(this, body, this.intSet, params);
    let ok = true, any = false;
    const visit = (n) => {
      if (ts.isFunctionLike(n) && n !== this.node) return;
      if (ts.isReturnStatement(n) && n.expression) {
        any = true;
        if (!isIntExpr(this, n.expression, this.intSet, params)) ok = false;
      }
      ts.forEachChild(n, visit);
    };
    visit(body);
    return ok && any;
  }

  // -- lowering ---------------------------------------------------------

  lower() {
    const ml = this.ml, node = this.node, sig = this.sig;
    this.intSet = this.intVars();
    for (const p of sig.params) this.env[p.name] = p.ty;
    const anchor = this.f.stmt || node || this.f.classNode;
    const fn = {
      name: this.f.name,
      loc: ml.loc(anchor),
      end_line: ml.sf.getLineAndCharacterOfPosition(anchor.getEnd()).line + 1,
      params: sig.params.map((p) => [p.name, p.ty]),
      ret: sig.ret,
      requires: [],
      ensures: [],
      decreases: null,
      raises: [],
      body: [],
      intents: [],
      mirrors: [],
      unsupported: this.unsupported,
      trusted: false,
      exported: this.f.exported,
      source: anchor.getText(ml.sf),
      locals: {},
      escaped: [],
    };
    this.fn = fn;
    for (const cl of sig.contracts) {
      cl.consumed = true;
      try {
        this.functionContract(cl);
      } catch (e) {
        if (!(e instanceof LowerError)) throw e;
        this.unsupported.push([`contract: ${e.message}`, e.line || cl.line]);
      }
    }
    if (this.f.ctor) {
      fn.body = this.constructorBody();
      fn.locals = { ...this.env };
      fn.intents = this.intents;
      return fn;
    }
    this.scanClosures(node);
    const body = node.body;
    const entry = [];
    for (const [pname, pat] of sig.destructs || []) {
      try {
        this.destructureFrom(pat, { e: "Var", ty: this.env[pname], loc: ml.loc(pat), name: pname }, pat, ml.loc(pat), false, entry);
      } catch (e) {
        if (!(e instanceof LowerError)) throw e;
        this.unsupported.push([e.message, e.line || ml.line(pat)]);
      }
    }
    if (ts.isBlock(body)) fn.body = entry.concat(this.block(body.statements, body));
    else {
      try {
        const v = this.coerce(this.expr(body, sig.ret), sig.ret);
        fn.body = entry.concat([{ s: "Return", loc: ml.loc(body), value: v }]);
      } catch (e) {
        if (!(e instanceof LowerError)) throw e;
        this.unsupported.push([e.message, e.line || ml.line(body)]);
        fn.body = [{ s: "Unsupported", loc: ml.loc(body), reason: e.message }];
      }
    }
    if (sig.ret.k === "opaque" && sig.ret.why === "unannotated return" && ts.isBlock(body)) {
      // without an annotation the function's type includes undefined: falling off the end returns it
      fn.body.push({ s: "Return", loc: [fn.end_line, 0, 0], value: this.coerce({ e: "Lit", ty: NONE, loc: [fn.end_line, 0, 0], value: null }, sig.ret) });
    }
    fn.locals = { ...this.env };
    fn.escaped = Object.keys(this.env).filter((n) => this.escaped.has(n.split("$")[0]) && n !== "self");
    fn.intents = this.intents;
    return fn;
  }

  // A class's constructor: parameter properties, then field initializers,
  // then the constructor body (JavaScript's order).
  constructorBody() {
    const ml = this.ml, cls = this.f.cls, node = this.node;
    const c = ml.classes[cls];
    const out = [];
    const self = { e: "Var", ty: classOf(cls), loc: ml.loc(c.node), name: "self" };
    const fieldTy = (n) => (c.fields.find((x) => x[0] === n) || [null, null])[1];
    if (node) {
      for (const p of node.parameters) {
        const isProp = p.modifiers && p.modifiers.some((x) => [ts.SyntaxKind.PublicKeyword, ts.SyntaxKind.PrivateKeyword, ts.SyntaxKind.ProtectedKeyword, ts.SyntaxKind.ReadonlyKeyword].includes(x.kind));
        if (isProp && ts.isIdentifier(p.name)) {
          const ft = fieldTy(p.name.text);
          const v = { e: "Var", ty: this.env[p.name.text], loc: ml.loc(p), name: p.name.text };
          out.push({ s: "FieldAssign", loc: ml.loc(p), obj: self, cls, field: p.name.text, value: this.coerce(v, ft) });
        }
      }
    }
    for (const m of c.node.members) {
      if (ts.isPropertyDeclaration(m) && ts.isIdentifier(m.name) && !(m.modifiers && m.modifiers.some((x) => x.kind === ts.SyntaxKind.StaticKeyword))) {
        const ft = fieldTy(m.name.text);
        if (!m.initializer) continue;
        try {
          const v = this.coerce(this.expr(m.initializer, ft), ft);
          out.push({ s: "FieldAssign", loc: ml.loc(m), obj: self, cls, field: m.name.text, value: v });
        } catch (e) {
          if (!(e instanceof LowerError)) throw e;
          this.unsupported.push([e.message, e.line || ml.line(m)]);
          out.push({ s: "Unsupported", loc: ml.loc(m), reason: e.message });
        }
      }
    }
    if (node && node.body) {
      this.scanClosures(node);
      out.push(...this.block(node.body.statements, node.body));
    }
    return out;
  }

  // Closures capture enclosing variables by reference, and JavaScript lets
  // them reassign those variables. A local function called directly may
  // change what it captures; one that escapes (passed or stored anywhere)
  // may be run by unchecked code at any later unchecked call.
  scanClosures(node) {
    if (!node || !node.body) return;
    const called = new Set();
    const walk = (n, inFn) => {
      if (ts.isCallExpression(n) && ts.isIdentifier(n.expression)) called.add(n.expression);
      ts.forEachChild(n, (x) => walk(x, inFn));
    };
    walk(node.body, false);
    const captured = (fnNode) => {
      const out = new Set();
      const v = (n) => {
        if (ts.isIdentifier(n)) out.add(n.text);
        ts.forEachChild(n, v);
      };
      v(fnNode.body || fnNode);
      return out;
    };
    const visit = (n) => {
      if (n !== node && (ts.isFunctionDeclaration(n) || ts.isArrowFunction(n) || ts.isFunctionExpression(n))) {
        const caps = captured(n);
        let name = null;
        if (ts.isFunctionDeclaration(n) && n.name) name = n.name.text;
        else if (ts.isVariableDeclaration(n.parent) && ts.isIdentifier(n.parent.name)) name = n.parent.name.text;
        if (name) this.closures.set(name, caps);
        // An inline callback is handed to whoever is called with it.
        const inlineArg = ts.isCallExpression(n.parent) && n.parent.arguments.includes(n);
        const isForEach = inlineArg && ts.isPropertyAccessExpression(n.parent.expression) && n.parent.expression.name.text === "forEach";
        const quant = inlineArg && ts.isPropertyAccessExpression(n.parent.expression) && ["every", "some", "map", "filter", "reduce", "find", "findIndex", "sort"].includes(n.parent.expression.name.text);
        if (inlineArg && !isForEach && !quant) caps.forEach((x) => this.escaped.add(x));
        if (quant && this.mutatesCaptured(n)) caps.forEach((x) => this.escaped.add(x));
        return; // nested functions are opaque; do not descend
      }
      if (ts.isIdentifier(n) && this.closures.has(n.text) && !called.has(n) && !(ts.isVariableDeclaration(n.parent) && n.parent.name === n) && !(ts.isFunctionDeclaration(n.parent) && n.parent.name === n)) {
        this.closures.get(n.text).forEach((x) => this.escaped.add(x));
      }
      ts.forEachChild(n, visit);
    };
    visit(node.body);
  }

  mutatesCaptured(fnNode) {
    let m = false;
    const v = (n) => {
      if (ts.isBinaryExpression(n) && n.operatorToken.kind >= ts.SyntaxKind.FirstAssignment && n.operatorToken.kind <= ts.SyntaxKind.LastAssignment) m = true;
      if ((ts.isPrefixUnaryExpression(n) || ts.isPostfixUnaryExpression(n)) && (n.operator === ts.SyntaxKind.PlusPlusToken || n.operator === ts.SyntaxKind.MinusMinusToken)) m = true;
      if (ts.isCallExpression(n)) m = true;
      ts.forEachChild(n, v);
    };
    v(fnNode.body);
    return m;
  }

  functionContract(cl) {
    const kw = cl.keyword;
    if (kw === "intent") {
      const { ids, text } = parseIntent(cl);
      if (text !== null) this.ml.module.intents.push({ id: ids[0], text, line: cl.line, col: cl.col });
      for (const i of ids) if (!this.intents.includes(i)) this.intents.push(i);
      this.currentIntents = ids;
      return;
    }
    if (kw === "mirrors") {
      this.fn.mirrors.push([cl.payload.trim(), cl.line]);
      return;
    }
    if (kw === "trusted") {
      this.fn.trusted = true;
      return;
    }
    if (kw === "pure") return;
    const tags = cl.tags.length ? cl.tags : this.currentIntents;
    for (const t of tags) if (!this.intents.includes(t)) this.intents.push(t);
    if (kw === "requires") this.fn.requires.push(this.clause(cl, "requires", tags));
    else if (kw === "ensures") this.fn.ensures.push(this.clause(cl, "ensures", tags, this.sig.ret));
    else if (kw === "decreases") this.fn.decreases = this.clause(cl, "decreases", tags, null, INT);
    else if (kw === "raises") this.fn.raises.push(this.clause(cl, "raises", tags));
  }

  clause(cl, kind, tags = [], resultTy = null, expect = BOOL) {
    const text = cl.payload;
    if (!text) throw this.err(`empty '@${kind}'`, cl.line);
    const src = ts.createSourceFile("spec.ts", "(" + text + "\n)", ts.ScriptTarget.Latest, true);
    const st = src.statements[0];
    if (!st || !ts.isExpressionStatement(st) || src.statements.length !== 1 || src.parseDiagnostics.length) throw this.err(`cannot parse '@${kind}' as a TypeScript expression`, cl.line);
    const saved = { spec: this.spec, result: this.resultTy, specSf: this.specSf, specLine: this.specLine, specCol: this.specCol };
    this.spec = true;
    this.resultTy = resultTy;
    this.specSf = src;
    this.specLine = cl.line;
    this.specCol = cl.payloadCol - 1;
    try {
      let e = this.expr(st.expression);
      if (expect.k === "bool") e = this.truthy(e, st.expression);
      else if (e.ty.k !== "int") throw this.err(`'@${kind}' must be an int expression`, cl.line);
      const loc = [cl.line, cl.payloadCol, text.includes("\n") ? 0 : cl.payloadCol + text.length];
      return { kind, expr: e, loc, text: text.split(/\s+/).join(" "), intents: tags };
    } finally {
      Object.assign(this, { spec: saved.spec, resultTy: saved.result, specSf: saved.specSf, specLine: saved.specLine, specCol: saved.specCol });
    }
  }

  nloc(node) {
    if (this.spec && this.specSf) {
      const s = this.specSf.getLineAndCharacterOfPosition(node.getStart(this.specSf));
      const e = this.specSf.getLineAndCharacterOfPosition(node.getEnd());
      const line = this.specLine + s.line;
      const col = s.line === 0 ? this.specCol + s.character : s.character;
      const ecol = e.line === s.line ? (s.line === 0 ? this.specCol + e.character : e.character) : 0;
      return [line, col, ecol];
    }
    return this.ml.loc(node);
  }
  nline(node) {
    return this.nloc(node)[0];
  }

  // -- statements --------------------------------------------------------

  blockContracts(block, stmts) {
    // assert/assume comments inside this block, not inside a child statement
    const open = block.getStart(this.ml.sf), close = block.getEnd();
    return this.localContracts.filter(
      (cl) => !cl.consumed && STMT_KW.has(cl.keyword) && cl.pos > open && cl.pos < close && !stmts.some((s) => cl.pos >= s.getStart(this.ml.sf) && cl.pos < s.getEnd())
    );
  }

  blockBody(block) {
    return this.block(block.statements, block);
  }

  block(stmts, block) {
    const out = [];
    const pending = block ? this.blockContracts(block, stmts) : [];
    for (const s of stmts) {
      const start = s.getStart(this.ml.sf);
      for (const cl of pending.filter((c) => !c.consumed && c.pos < start)) out.push(...this.stmtContract(cl));
      out.push(...this.stmt(s));
    }
    for (const cl of pending.filter((c) => !c.consumed)) out.push(...this.stmtContract(cl));
    return out;
  }

  stmtContract(cl) {
    cl.consumed = true;
    try {
      const c = this.clause(cl, cl.keyword, cl.tags);
      return [{ s: cl.keyword === "assert" ? "AssertStmt" : "AssumeStmt", loc: c.loc, clause: c, native: false }];
    } catch (e) {
      if (!(e instanceof LowerError)) throw e;
      this.unsupported.push([e.message, e.line || cl.line]);
      return [{ s: "Unsupported", loc: [cl.line, 0, 0], reason: e.message }];
    }
  }

  stmt(s) {
    try {
      return this._stmt(s);
    } catch (e) {
      if (!(e instanceof LowerError)) throw e;
      const line = e.line || this.ml.line(s);
      this.unsupported.push([e.message, line]);
      return [{ s: "Unsupported", loc: [line, 0, 0], reason: e.message }];
    }
  }

  inner(s) {
    return this.scoped(() => (ts.isBlock(s) ? this.blockBody(s) : this.stmt(s)));
  }

  // -- scopes ------------------------------------------------------------
  // JavaScript `let`/`const` are block-scoped. Every declaration gets a
  // unique IR name, lookups walk the scope chain, and shadowing an outer
  // name is rejected (it is legal JS, but an easy way to fool a reader).

  scoped(f) {
    this.scopes.push(new Map());
    try {
      return f();
    } finally {
      this.scopes.pop();
    }
  }

  resolve(name) {
    for (let i = this.scopes.length - 1; i >= 0; i--) if (this.scopes[i].has(name)) return this.scopes[i].get(name);
    return null;
  }

  bindLocal(name, ty, node) {
    if (this.resolve(name) !== null) throw this.err(`'${name}' shadows a variable of the same name; telic requires distinct names`, node);
    let ir = name;
    if (this.usedIr.has(ir)) {
      let k = 2;
      while (this.usedIr.has(`${name}$${k}`)) k++;
      ir = `${name}$${k}`;
    }
    this.usedIr.add(ir);
    this.scopes[this.scopes.length - 1].set(name, ir);
    this.env[ir] = ty;
    return ir;
  }

  varOf(name, node) {
    const ir = this.resolve(name);
    if (ir === null) throw this.err(`unknown variable '${name}'`, node);
    return ir;
  }

  declare(name, ty, node) {
    const old = this.env[name];
    if (!old) this.env[name] = ty;
    else if (!tyEq(old, ty)) {
      if (old.k === "real" && ty.k === "int") return;
      if (old.k === "opaque" || ty.k === "opaque") return;
      if (old.k === "option" && (tyEq(old.inner, ty) || ty.k === "none")) return;
      if (old.k === "list" && ty.k === "list" && ty.elem.k === "none") return;
      throw this.err(`variable '${name}' changes type from ${tyStr(old)} to ${tyStr(ty)}`, node);
    }
  }

  coerce(e, ty) {
    if (!ty || tyEq(e.ty, ty)) return e;
    if (ty.k !== "opaque" && e.ty.k !== "opaque" && e.ty.k !== "none" && (hasOpaque(e.ty) || hasOpaque(ty)) && !(ty.k === "option" && tyEq(ty.inner, e.ty))) return { e: "Builtin", ty, loc: e.loc, name: "from_opaque", args: [e] };
    if (e.ty.k === "opaque" && ty.k !== "none") {
      if (e.e === "Extern") return { ...e, ty };
      return { e: "Builtin", ty, loc: e.loc, name: "from_opaque", args: [e] };
    }
    if (ty.k === "opaque") return { e: "Builtin", ty, loc: e.loc, name: "to_opaque", args: [e.ty.k === "none" ? { e: "Lit", ty: INT, loc: e.loc, value: 0 } : e] };
    if (ty.k === "option") {
      if (e.ty.k === "none") return { e: "Lit", ty, loc: e.loc, value: null };
      if (e.ty.k !== "option") return { e: "Builtin", ty, loc: e.loc, name: "some", args: [this.coerce(e, ty.inner)] };
      return e;
    }
    if (e.ty.k === "option" && ty.k !== "none") return this.coerce(this.unwrap(e), ty);
    if (ty.k === "real" && e.ty.k === "int") return { e: "Builtin", ty: REAL, loc: e.loc, name: "to_real", args: [e] };
    if (ty.k === "list" && e.e === "ListLit" && e.elems.length === 0) return { ...e, ty };
    if (ty.k === "dict" && e.e === "Builtin" && e.name === "dict_lit" && e.args.length === 0) return { ...e, ty };
    return e;
  }

  // A list-valued expression that denotes a new array (binding it creates no alias).
  freshList(e) {
    if (e.e === "Extern" && /^Array\.(sort|reverse|fill|copyWithin)$/.test(e.name)) return false;
    if (e.e === "ListLit" || e.e === "Call" || e.e === "Extern" || e.e === "New") return true;
    if (e.e === "Builtin" && ["slice", "comp", "dict_lit", "dict_copy", "from_opaque", "dict_keys", "dict_values", "list_append", "list_concat"].includes(e.name)) return true;
    if (e.e === "Builtin" && e.name === "same_len") return this.freshList(e.args[1]);
    if (e.e === "Builtin" && e.name === "await") return this.freshList(e.args[0]);
    if (e.e === "Ite") return this.freshList(e.then) && this.freshList(e.orelse);
    return false;
  }

  noAlias(name, v, node) {
    if (v.ty.k !== "list" && v.ty.k !== "dict") return;
    if (!this.freshList(v)) throw this.err(`'${name} = ...' would alias an existing array; telic models arrays as values, so copy with .slice()`, node);
  }

  loopContracts(s) {
    const out = [];
    const byLine = new Map();
    for (const cl of this.localContracts) for (const l of cl.rawLines) byLine.set(l, cl);
    for (let ln = this.ml.line(s) - 1; ln >= 1; ln--) {
      const t = this.ml.lines[ln - 1].trim();
      if (!t.startsWith("//")) break;
      const cl = byLine.get(ln);
      if (cl && LOOP_KW.has(cl.keyword) && !cl.consumed && !out.includes(cl)) out.push(cl);
    }
    out.reverse();
    const body = s.statement;
    if (body && ts.isBlock(body)) {
      const open = body.getStart(this.ml.sf);
      const limit = body.statements.length ? body.statements[0].getStart(this.ml.sf) : body.getEnd();
      for (const cl of this.localContracts) if (cl.pos > open && cl.pos < limit && LOOP_KW.has(cl.keyword) && !cl.consumed && !out.includes(cl)) out.push(cl);
    }
    for (const cl of out) cl.consumed = true;
    return out;
  }

  loopClauses(cls) {
    const invs = [];
    let dec = null, index = null;
    for (const cl of cls) {
      if (cl.keyword === "invariant") invs.push(this.clause(cl, "invariant", cl.tags));
      else if (cl.keyword === "decreases") dec = this.clause(cl, "decreases", cl.tags, null, INT);
      else if (cl.keyword === "index") index = cl.payload.trim();
    }
    return { invs, dec, index };
  }

  assignTo(srcName, valueNode, node, op = null) {
    const loc = this.ml.loc(node);
    const name = this.varOf(srcName, node);
    let known = this.env[name];
    if (this.sig.params.some((p) => p.name === name) && known.k === "list") throw this.err(`rebinding array parameter '${srcName}' is not supported`, node);
    if (this.consts.has(name)) throw this.err(`cannot assign to const '${srcName}'`, node);
    if (known.k === "none" && !op) {
      // let x = null; ... x = v: an optional of v's type
      const v0 = this.expr(valueNode, null);
      if (v0.ty.k !== "none" && !["option", "list", "dict"].includes(v0.ty.k)) {
        known = v0.ty.k === "opaque" ? v0.ty : optionOf(v0.ty);
        this.env[name] = known;
      }
    }
    let v = this.expr(valueNode, known);
    if (op) {
      const cur = { e: "Var", ty: known, loc, name };
      v = this.arith(op, cur, v, node);
    }
    v = this.coerce(v, known);
    this.noAlias(srcName, v, node);
    if (!tyEq(v.ty, known) && !(known.k === "list" && v.ty.k === "list" && v.ty.elem.k === "none")) throw this.err(`cannot assign ${tyStr(v.ty)} to '${srcName}' of type ${tyStr(known)}`, node);
    return [{ s: "Assign", loc, name, value: v }];
  }

  // console.* output is ignored, but its arguments are still evaluated.
  logEffects(args, loc) {
    const out = [];
    for (const a of args) {
      const parts = ts.isTemplateExpression(a) ? a.templateSpans.map((sp) => sp.expression) : [a];
      for (const part of parts) {
        try {
          out.push({ s: "ExprStmt", loc, expr: this.expr(part) });
        } catch (e) {
          if (!(e instanceof LowerError)) throw e;
          let hasCall = false;
          const walk = (n) => {
            if (ts.isCallExpression(n) || ts.isNewExpression(n)) hasCall = true;
            ts.forEachChild(n, walk);
          };
          walk(part);
          if (hasCall) throw e;
        }
      }
    }
    return out;
  }

  exprStatement(e, node) {
    const K = ts.SyntaxKind;
    const loc = this.ml.loc(node);
    if (ts.isParenthesizedExpression(e)) return this.exprStatement(e.expression, node);
    if (ts.isBinaryExpression(e)) {
      const k = e.operatorToken.kind;
      const ops = { [K.PlusEqualsToken]: "add", [K.MinusEqualsToken]: "sub", [K.AsteriskEqualsToken]: "mul", [K.SlashEqualsToken]: "rdiv", [K.PercentEqualsToken]: "tmod" };
      if (k === K.QuestionQuestionEqualsToken || k === K.BarBarEqualsToken) {
        // x ??= v  ==>  x = x ?? v
        const fake = ts.factory.createBinaryExpression(e.left, k === K.QuestionQuestionEqualsToken ? K.QuestionQuestionToken : K.BarBarToken, e.right);
        ts.setTextRange(fake, e);
        fake.parent = e.parent;
        return this.exprStatement(ts.factory.createBinaryExpression(e.left, K.EqualsToken, fake), node);
      }
      if (k === K.EqualsToken || ops[k]) {
        if (ts.isIdentifier(e.left)) return this.assignTo(e.left.text, e.right, node, ops[k] || null);
        if (ts.isPropertyAccessExpression(e.left)) return this.assignProperty(e.left, e.right, node, ops[k] || null);
        if (ts.isElementAccessExpression(e.left) && !(ts.isIdentifier(e.left.expression) && this.env[this.resolve(e.left.expression.text)]?.k === "list")) return this.assignElement(e.left, e.right, node, ops[k] || null);
        if (ts.isElementAccessExpression(e.left) && ts.isIdentifier(e.left.expression)) {
          const name = this.varOf(e.left.expression.text, node);
          const t = this.env[name];
          if (!t || t.k !== "list") throw this.err(`'${e.left.expression.text}[...] = ...' needs an array`, node);
          const idx = this.index(e.left.argumentExpression);
          let v = this.expr(e.right, t.elem);
          if (ops[k]) v = this.arith(ops[k], { e: "Index", ty: t.elem, loc, seq: { e: "Var", ty: t, loc, name }, idx, wrap: false }, v, node);
          v = this.coerce(v, t.elem);
          if (!tyEq(v.ty, t.elem)) throw this.err(`cannot store ${tyStr(v.ty)} into ${tyStr(t)}`, node);
          return [{ s: "IndexAssign", loc, name, idx, value: v, wrap: false }];
        }
        throw this.err(`unsupported assignment target '${e.left.getText(this.ml.sf)}'`, node);
      }
    }
    if ((ts.isPostfixUnaryExpression(e) || ts.isPrefixUnaryExpression(e)) && (e.operator === K.PlusPlusToken || e.operator === K.MinusMinusToken) && (ts.isPropertyAccessExpression(e.operand) || ts.isElementAccessExpression(e.operand))) {
      const one = ts.factory.createNumericLiteral(1);
      ts.setTextRange(one, e);
      one.parent = e;
      return ts.isPropertyAccessExpression(e.operand) ? this.assignProperty(e.operand, one, node, e.operator === K.PlusPlusToken ? "add" : "sub") : this.assignElement(e.operand, one, node, e.operator === K.PlusPlusToken ? "add" : "sub");
    }
    if ((ts.isPostfixUnaryExpression(e) || ts.isPrefixUnaryExpression(e)) && (e.operator === K.PlusPlusToken || e.operator === K.MinusMinusToken)) {
      if (!ts.isIdentifier(e.operand)) throw this.err("++/-- is supported on variables only", node);
      const name = this.varOf(e.operand.text, node);
      if (this.consts.has(name)) throw this.err(`cannot assign to const '${e.operand.text}'`, node);
      const t = this.env[name];
      if (!isNum(t)) throw this.err(`'${e.operand.text}' is not a number`, node);
      const one = { e: "Lit", ty: t, loc, value: 1 };
      const cur = { e: "Var", ty: t, loc, name };
      return [{ s: "Assign", loc, name, value: { e: "Binary", ty: t, loc, op: e.operator === K.PlusPlusToken ? "add" : "sub", left: cur, right: one } }];
    }
    if (ts.isCallExpression(e)) {
      const c = e.expression;
      if (ts.isPropertyAccessExpression(c) && ts.isIdentifier(c.expression) && c.expression.text === "console" && this.resolve("console") === null) return this.logEffects(e.arguments, loc);
      if (ts.isPropertyAccessExpression(c) && c.name.text === "forEach" && e.arguments.length === 1 && (ts.isArrowFunction(e.arguments[0]) || ts.isFunctionExpression(e.arguments[0]))) {
        const r = this.forEachLoop(c.expression, e.arguments[0], node);
        if (r) return r;
      }
      if (ts.isPropertyAccessExpression(c) && ["set", "delete"].includes(c.name.text)) {
        const target = this.expr(c.expression);
        if (target.ty.k === "dict") return this.mapWrite(target, c.name.text, e.arguments, node);
      }
      if (ts.isPropertyAccessExpression(c) && c.name.text === "push" && ts.isPropertyAccessExpression(c.expression)) {
        const fld = this.expr(c.expression);
        if (fld.e === "Field" && fld.obj.ty.k === "class" && fld.ty.k === "list" && e.arguments.length === 1) {
          const v = this.coerce(this.expr(e.arguments[0], fld.ty.elem), fld.ty.elem);
          return [{ s: "FieldAssign", loc, obj: fld.obj, cls: fld.obj.ty.name, field: fld.name, value: { e: "Builtin", ty: fld.ty, loc, name: "list_append", args: [fld, v] } }];
        }
      }
      if (ts.isPropertyAccessExpression(c) && c.name.text === "unshift" && ts.isIdentifier(c.expression) && e.arguments.length === 1 && !ts.isSpreadElement(e.arguments[0])) {
        // xs.unshift(v): xs = [v] + xs
        const name = this.varOf(c.expression.text, node);
        let t = this.env[name];
        if (t && t.k === "list") {
          const v0 = this.expr(e.arguments[0], t.elem.k === "none" ? null : t.elem);
          if (t.elem.k === "none") {
            t = listOf(v0.ty);
            this.env[name] = t;
          }
          const v = this.coerce(v0, t.elem);
          return [{ s: "Assign", loc, name, value: { e: "Builtin", ty: t, loc, name: "list_concat", args: [{ e: "ListLit", ty: t, loc, elems: [v] }, { e: "Var", ty: t, loc, name }] } }];
        }
      }
      if (ts.isPropertyAccessExpression(c) && c.name.text === "push" && ts.isIdentifier(c.expression)) {
        const name = this.varOf(c.expression.text, node);
        let t = this.env[name];
        if (t && t.k === "opaque") return [{ s: "ExprStmt", loc, expr: this.extern(`${c.expression.text}.push`, [{ e: "Var", ty: t, loc, name }, ...e.arguments.map((a) => this.coerce(this.expr(a), opaque("")))], NONE, loc) }];
        if (!t || t.k !== "list") throw this.err(`'${c.expression.text}.push' needs an array`, node);
        if (e.arguments.length === 1 && ts.isSpreadElement(e.arguments[0])) {
          // xs.push(...ys): xs = xs + ys
          let ys = this.expr(e.arguments[0].expression, t.elem.k === "none" ? null : t);
          if (ys.ty.k === "opaque") ys = this.coerce(ys, t.elem.k === "none" ? listOf(opaque("")) : t);
          if (ys.ty.k !== "list") throw this.err("push(...xs) needs an array", node);
          if (t.elem.k === "none") {
            t = ys.ty;
            this.env[name] = t;
          }
          if (!tyEq(ys.ty, t)) throw this.err(`cannot push ${tyStr(ys.ty)} onto ${tyStr(t)}`, node);
          return [{ s: "Assign", loc, name, value: { e: "Builtin", ty: t, loc, name: "list_concat", args: [{ e: "Var", ty: t, loc, name }, ys] } }];
        }
        if (e.arguments.length !== 1) throw this.err("push takes one argument here", node);
        const v0 = this.expr(e.arguments[0], t.elem.k === "none" ? null : t.elem);
        if (t.elem.k === "none") {
          t = listOf(v0.ty);
          this.env[name] = t;
        }
        const v = this.coerce(v0, t.elem);
        return [{ s: "Append", loc, name, value: v }];
      }
      return [{ s: "ExprStmt", loc, expr: this.expr(e) }];
    }
    if (ts.isAwaitExpression(e) || ts.isNewExpression(e)) return [{ s: "ExprStmt", loc, expr: this.expr(e) }];
    if (ts.isDeleteExpression(e) && ts.isElementAccessExpression(e.expression)) {
      const target = this.expr(e.expression.expression);
      if (target.ty.k === "dict") return this.mapWrite(target, "delete", [e.expression.argumentExpression], node);
    }
    if (ts.isIdentifier(e) || ts.isStringLiteral(e) || e.kind === K.VoidExpression) return [];
    throw this.err(`unsupported expression statement '${e.getText(this.ml.sf).slice(0, 40)}'`, node);
  }

  // obj.f = v / obj.f += v / this.f = v
  assignProperty(target, valueNode, node, op) {
    const loc = this.ml.loc(node);
    const obj = this.unwrap(this.expr(target.expression));
    const name = target.name.text;
    if (obj.ty.k === "opaque") return [{ s: "ExprStmt", loc, expr: this.extern(`set .${name}`, [obj, this.coerce(this.expr(valueNode), opaque(""))], NONE, loc) }];
    if (obj.ty.k === "dict" && obj.ty.js === "object") return this.mapWrite(obj, "set", [null, valueNode], node, { e: "Lit", ty: STR, loc, value: name }, op);
    if (obj.ty.k !== "class") throw this.err(`cannot assign '.${name}' on ${tyStr(obj.ty)}`, node);
    const cls = obj.ty.name;
    const c = this.ml.classes[cls];
    const key = `${cls}.${name}`;
    if (c.setters.has(key)) {
      const sig = this.ml.sigs[`${key}.setter`];
      const pt = sig && sig.params[1] ? sig.params[1].ty : opaque("");
      return [{ s: "ExprStmt", loc, expr: { e: "Call", ty: NONE, loc, func: `${key}.setter`, args: [obj, this.coerce(this.expr(valueNode, pt), pt)] } }];
    }
    if (c.props.has(key)) return [{ s: "Raise", loc, what: `TypeError: '${name}' of ${cls} has a getter and no setter`, caught: this.tryDepth > 0 }];
    const f = c.fields.find((x) => x[0] === name);
    if (!f) throw this.err(`${cls} has no field '${name}' (declare it in the class)`, node);
    let v = this.expr(valueNode, f[1]);
    if (op) v = this.arith(op, { e: "Field", ty: f[1], loc, obj, name }, v, node);
    v = this.coerce(v, f[1]);
    if (["list", "dict"].includes(f[1].k) && !this.freshList(v)) throw this.err(`storing an existing ${tyStr(f[1])} in a field would alias it; store a copy`, node);
    return [{ s: "FieldAssign", loc, obj, cls, field: name, value: v }];
  }

  // d[k] = v for maps/records, obj.xs[i] = v, obj.d[k] = v, opaque[k] = v
  assignElement(target, valueNode, node, op) {
    const loc = this.ml.loc(node);
    const base = this.unwrap(this.expr(target.expression));
    if (base.ty.k === "opaque") return [{ s: "ExprStmt", loc, expr: this.extern("setitem", [base, this.expr(target.argumentExpression), this.coerce(this.expr(valueNode), opaque(""))], NONE, loc) }];
    if (base.ty.k === "dict") return this.mapWrite(base, "set", [target.argumentExpression, valueNode], node, null, op);
    if (base.ty.k === "list" && base.e === "Field" && base.obj.ty.k === "class") {
      const i = this.index(target.argumentExpression);
      let v = this.expr(valueNode, base.ty.elem);
      if (op) v = this.arith(op, { e: "Index", ty: base.ty.elem, loc, seq: base, idx: i, wrap: false }, v, node);
      v = this.coerce(v, base.ty.elem);
      return [{ s: "FieldAssign", loc, obj: base.obj, cls: base.obj.ty.name, field: base.name, value: { e: "Builtin", ty: base.ty, loc, name: "list_set", args: [base, i, v] } }];
    }
    throw this.err(`unsupported assignment target '${target.getText(this.ml.sf).slice(0, 40)}'`, node);
  }

  // m.set(k, v) / m.delete(k) / d[k] = v on a variable or a field
  mapWrite(d, m, args, node, keyExpr = null, op = null) {
    const loc = this.ml.loc(node);
    const t = d.ty;
    const k = this.coerce(keyExpr || this.expr(args[0]), t.key);
    if (m === "delete") {
      if (d.e === "Var") return [{ s: "DictDel", loc, name: d.name, key: k, strict: false }];
      if (d.e === "Field" && d.obj.ty.k === "class") return [{ s: "FieldAssign", loc, obj: d.obj, cls: d.obj.ty.name, field: d.name, value: { e: "Builtin", ty: t, loc, name: "dict_remove", args: [d, k] } }];
      throw this.err("'.delete()' on a map that is not a variable or field is not tracked", node);
    }
    let v = this.expr(args[1], t.val);
    if (op) v = this.arith(op, { e: "Index", ty: t.val, loc, seq: d, idx: k, wrap: false }, v, node);
    v = this.coerce(v, t.val);
    if (d.e === "Var") return [{ s: "IndexAssign", loc, name: d.name, idx: k, value: v, wrap: false }];
    if (d.e === "Field" && d.obj.ty.k === "class") return [{ s: "FieldAssign", loc, obj: d.obj, cls: d.obj.ty.name, field: d.name, value: { e: "Builtin", ty: t, loc, name: "dict_set", args: [d, k, v] } }];
    throw this.err("writing to a map that is not a variable or field is not tracked", node);
  }

  // xs.forEach((x, i) => { ... })  ==>  a for-of loop (return = continue)
  forEachLoop(seqNode, fnNode, node) {
    const seq = this.unwrap(this.expr(seqNode));
    if (seq.ty.k !== "list" || fnNode.parameters.length > 2 || !fnNode.parameters.every((p) => ts.isIdentifier(p.name))) return null;
    const loc = this.ml.loc(node);
    return this.scoped(() => {
      const idxName = fnNode.parameters[1] ? fnNode.parameters[1].name.text : null;
      const idx = idxName ? this.bindLocal(idxName, INT, node) : `i$${++this.tmp}`;
      if (!idxName) this.env[idx] = INT;
      const elem = fnNode.parameters[0] ? this.bindLocal(fnNode.parameters[0].name.text, seq.ty.elem, node) : `x$${++this.tmp}`;
      if (!fnNode.parameters[0]) this.env[elem] = seq.ty.elem;
      this.callbackDepth = (this.callbackDepth || 0) + 1;
      try {
        const body = ts.isBlock(fnNode.body) ? this.scoped(() => this.blockBody(fnNode.body)) : [{ s: "ExprStmt", loc, expr: this.expr(fnNode.body) }];
        return [{ s: "ForEach", loc, elem, idx, seq, invariants: [], body, idx_visible: !!idxName }];
      } finally {
        this.callbackDepth--;
      }
    });
  }

  varDecls(list, node, loc) {
    if (!(list.flags & (ts.NodeFlags.Let | ts.NodeFlags.Const))) throw this.err("'var' is function-scoped and hoisted; use let or const", node);
    const isConst = !!(list.flags & ts.NodeFlags.Const);
    const out = [];
    for (const d of list.declarations) {
      if ((ts.isObjectBindingPattern(d.name) || ts.isArrayBindingPattern(d.name)) && d.initializer) {
        out.push(...this.destructure(d.name, d.initializer, node, loc, isConst));
        continue;
      }
      if (!ts.isIdentifier(d.name)) throw this.err("unsupported declaration", node);
      const src = d.name.text;
      if (d.initializer && (ts.isArrowFunction(d.initializer) || ts.isFunctionExpression(d.initializer))) {
        const name = this.bindLocal(src, opaque("closure"), node);
        this.consts.add(name);
        out.push({ s: "Assign", loc, name, value: this.opaqueOp("closure", [{ e: "Lit", ty: STR, loc, value: src }], opaque("closure"), loc) });
        continue;
      }
      let ty = d.type ? this.ml.typeOf(d.type, this.intSet.has(src)) : null;
      if (ty && ty.k === "real" && this.intSet.has(src)) ty = INT;
      if (!d.initializer) {
        // `let x;` holds undefined until assigned (a declared non-optional type must be assigned before use)
        const t = ty || opaque("declared without a type");
        const name = this.bindLocal(src, t, node);
        if (t.k === "opaque" || t.k === "option") out.push({ s: "Assign", loc, name, value: this.coerce({ e: "Lit", ty: NONE, loc, value: null }, t) });
        continue;
      }
      let v = this.expr(d.initializer, ty);
      if (!ty) {
        ty = v.ty;
        if (ty.k === "int" && !this.intSet.has(src)) ty = REAL;
      }
      v = this.coerce(v, ty);
      if (!tyEq(v.ty, ty) && !(ty.k === "list" && v.ty.k === "list" && v.ty.elem.k === "none")) throw this.err(`'${src}' is declared ${tyStr(ty)} but initialized with ${tyStr(v.ty)}`, node);
      this.noAlias(src, v, node);
      const name = this.bindLocal(src, ty, node);
      if (isConst) this.consts.add(name);
      out.push({ s: "Assign", loc, name, value: v });
    }
    return out;
  }

  destructure(pat, init, node, loc, isConst) {
    const out = [];
    let src = this.expr(init);
    if (src.e !== "Var") {
      const tmp = `destructure$${++this.tmp}`;
      this.env[tmp] = src.ty;
      out.push({ s: "Assign", loc, name: tmp, value: src });
      src = { e: "Var", ty: src.ty, loc, name: tmp };
    }
    this.destructureFrom(pat, src, node, loc, isConst, out);
    return out;
  }

  destructureFrom(pat, src, node, loc, isConst, out) {
    src = this.unwrap(src);
    pat.elements.forEach((el, i) => {
      if (ts.isOmittedExpression(el)) return;
      if (el.dotDotDotToken) {
        // ...rest: the remaining properties/elements
        if (!ts.isIdentifier(el.name)) throw this.err("nested rest destructuring is not supported", node);
        const rest = src.ty.k === "list" && ts.isArrayBindingPattern(pat) ? { e: "Builtin", ty: src.ty, loc, name: "slice", args: [src, { e: "Lit", ty: INT, loc, value: i }, { e: "Lit", ty: NONE, loc, value: null }] } : this.opaqueOp("rest", [this.coerce(src, opaque(""))], opaque(""), loc);
        const name = this.bindLocal(el.name.text, rest.ty, node);
        if (isConst) this.consts.add(name);
        out.push({ s: "Assign", loc, name, value: rest });
        return;
      }
      let v;
      if (ts.isObjectBindingPattern(pat)) {
        const prop = el.propertyName ? el.propertyName.getText(this.ml.sf) : el.name.text;
        v = src.ty.k === "record" || src.ty.k === "class" ? this.propertyOf(src, prop, node, loc) : src.ty.k === "dict" ? { e: "Builtin", ty: optionOf(src.ty.val), loc, name: "dict_get_opt", args: [src, this.coerce({ e: "Lit", ty: STR, loc, value: prop }, src.ty.key)] } : this.opaqueOp(`attr.${prop}`, [this.coerce(src, opaque(""))], opaque(""), loc);
      } else {
        if (src.ty.k === "list") v = { e: "Index", ty: src.ty.elem, loc, seq: src, idx: { e: "Lit", ty: INT, loc, value: i }, wrap: false };
        else v = this.opaqueOp(`item${i}`, [this.coerce(src, opaque(""))], opaque(""), loc);
      }
      if (el.initializer && v.ty.k === "option") {
        const dflt = this.coerce(this.expr(el.initializer, v.ty.inner), v.ty.inner);
        v = { e: "Ite", ty: v.ty.inner, loc, cond: { e: "Builtin", ty: BOOL, loc, name: "is_none", args: [v] }, then: dflt, orelse: this.unwrap(v) };
      }
      if (!ts.isIdentifier(el.name)) {
        // a nested pattern: destructure the property's value in turn
        const tmp = `destructure$${++this.tmp}`;
        this.env[tmp] = v.ty;
        out.push({ s: "Assign", loc, name: tmp, value: v });
        this.destructureFrom(el.name, { e: "Var", ty: v.ty, loc, name: tmp }, node, loc, isConst, out);
        return;
      }
      if (["list", "dict"].includes(v.ty.k) && !this.freshList(v)) throw this.err(`destructuring '${el.name.text}' would alias an existing ${tyStr(v.ty)}; copy it`, node);
      const name = this.bindLocal(el.name.text, v.ty, node);
      if (isConst) this.consts.add(name);
      out.push({ s: "Assign", loc, name, value: v });
    });
  }

  _stmt(s) {
    const K = ts.SyntaxKind;
    const loc = this.ml.loc(s);
    if (ts.isTryStatement(s)) {
      this.tryDepth += s.catchClause ? 1 : 0;
      let body;
      try {
        body = this.inner(s.tryBlock);
      } finally {
        this.tryDepth -= s.catchClause ? 1 : 0;
      }
      const handlers = [];
      if (s.catchClause) {
        handlers.push(
          this.scoped(() => {
            const pre = [];
            const v = s.catchClause.variableDeclaration;
            if (v && ts.isIdentifier(v.name)) {
              const name = this.bindLocal(v.name.text, opaque("exception"), s);
              pre.push({ s: "Assign", loc, name, value: { e: "Extern", ty: opaque("exception"), loc, name: "caught exception", args: [] } });
            }
            return pre.concat(this.blockBody(s.catchClause.block));
          })
        );
      }
      const fin = s.finallyBlock ? this.inner(s.finallyBlock) : [];
      return [{ s: "Try", loc, body, handlers, orelse: [], finalbody: fin }];
    }
    if (ts.isSwitchStatement(s)) return this.switchStmt(s, loc);
    if (ts.isFunctionDeclaration(s) && s.name) {
      const name = this.bindLocal(s.name.text, opaque("closure"), s);
      this.consts.add(name);
      return [{ s: "Assign", loc, name, value: this.opaqueOp("closure", [{ e: "Lit", ty: STR, loc, value: s.name.text }], opaque("closure"), loc) }];
    }
    if (ts.isClassDeclaration(s) || ts.isInterfaceDeclaration(s) || ts.isTypeAliasDeclaration(s)) return [];
    if (ts.isForInStatement(s)) return this.scoped(() => this.forIn(s, loc));
    if (ts.isReturnStatement(s) && this.callbackDepth) return [{ s: "Continue", loc }]; // return inside a forEach callback
    if (ts.isEmptyStatement(s)) return [];
    if (ts.isBlock(s)) return this.scoped(() => this.blockBody(s));
    if (ts.isVariableStatement(s)) return this.varDecls(s.declarationList, s, loc);
    if (ts.isExpressionStatement(s)) return this.exprStatement(s.expression, s);
    if (ts.isIfStatement(s)) {
      const c = this.cond(s.expression);
      const then = this.inner(s.thenStatement);
      const orelse = s.elseStatement ? this.inner(s.elseStatement) : [];
      return [{ s: "If", loc, cond: c, then, orelse }];
    }
    if (ts.isWhileStatement(s)) {
      const cls = this.loopContracts(s);
      const c = this.cond(s.expression);
      const body = this.inner(s.statement);
      const { invs, dec, index } = this.loopClauses(cls);
      if (index) throw this.err("'@index' only applies to for-of loops", s);
      return [{ s: "While", loc, cond: c, invariants: invs, decreases: dec, body, step: [] }];
    }
    if (ts.isForStatement(s)) return this.scoped(() => this.forStmt(s, loc));
    if (ts.isForOfStatement(s)) return this.scoped(() => this.forOf(s, loc));
    if (ts.isReturnStatement(s)) {
      if (!s.expression) return [{ s: "Return", loc, value: null }];
      if (this.sig.ret.k === "none") throw this.err("function returns a value but is declared void", s);
      const v = this.coerce(this.expr(s.expression, this.sig.ret), this.sig.ret);
      if (!tyEq(v.ty, this.sig.ret)) throw this.err(`returns ${tyStr(v.ty)} but is declared to return ${tyStr(this.sig.ret)}`, s);
      if (v.ty.k === "list" && !this.freshList(v) && !(v.e === "Var" && !this.sig.params.some((p) => p.name === v.name))) throw this.err("returning an array parameter (or an alias of one) would let the caller alias it; return a copy with .slice()", s);
      return [{ s: "Return", loc, value: v }];
    }
    if (s.kind === K.BreakStatement) {
      if (s.label) throw this.err("labelled break is not supported", s);
      return [{ s: "Break", loc }];
    }
    if (s.kind === K.ContinueStatement) {
      if (s.label) throw this.err("labelled continue is not supported", s);
      return [{ s: "Continue", loc }];
    }
    if (ts.isThrowStatement(s)) return [{ s: "Raise", loc, what: s.expression ? s.expression.getText(this.ml.sf).slice(0, 60) : "exception", caught: this.tryDepth > 0 }];
    throw this.err(`unsupported statement: ${K[s.kind]}`, s);
  }

  switchStmt(s, loc) {
    // switch (x) { case a: ...; break; ... default: ... }  ==>  if-chain.
    // Cases must end in break/return/throw/continue (or be empty, grouping
    // with the next case): fall-through into code is rejected.
    const subject = this.expr(s.expression);
    const clauses = s.caseBlock.clauses;
    const groups = [];
    let pending = [];
    for (const c of clauses) {
      pending.push(c);
      if (c.statements.length) {
        groups.push(pending);
        pending = [];
      }
    }
    if (pending.length) groups.push(pending);
    const ends = (stmts) => {
      const last = stmts[stmts.length - 1];
      return last && (last.kind === ts.SyntaxKind.BreakStatement || ts.isReturnStatement(last) || ts.isThrowStatement(last) || last.kind === ts.SyntaxKind.ContinueStatement || (ts.isBlock(last) && ends(last.statements)));
    };
    let chain = [];
    for (let gi = groups.length - 1; gi >= 0; gi--) {
      const g = groups[gi];
      const body = g[g.length - 1].statements;
      if (gi !== groups.length - 1 && body.length && !ends(body)) throw this.err("a switch case falls through into the next one; end it with break", g[0]);
      const stripped = body.length && body[body.length - 1].kind === ts.SyntaxKind.BreakStatement ? body.slice(0, -1) : body;
      const breaksOut = (x) => {
        let b = false;
        const v = (n) => {
          if (n.kind === ts.SyntaxKind.BreakStatement && !n.label && ts.findAncestor(n.parent, (p) => p === s || ts.isIterationStatement(p, false) || ts.isSwitchStatement(p)) === s) b = true;
          ts.forEachChild(n, v);
        };
        v(x);
        return b;
      };
      if (stripped.some(breaksOut)) throw this.err("break inside a nested block of a switch case is not supported", g[0]);
      const lowered = this.scoped(() => stripped.flatMap((x) => this.stmt(x)));
      const isDefault = g.some((c) => ts.isDefaultClause(c));
      if (isDefault) {
        chain = lowered;
        continue;
      }
      let cond = null;
      for (const c of g) {
        const v = this.coerce(this.expr(c.expression), subject.ty);
        const eq = { e: "Binary", ty: BOOL, loc, op: "eq", left: subject, right: v };
        cond = cond ? { e: "Binary", ty: BOOL, loc, op: "or", left: cond, right: eq } : eq;
      }
      chain = [{ s: "If", loc, cond, then: lowered, orelse: chain }];
    }
    return chain;
  }

  forIn(s, loc) {
    const d = s.initializer;
    if (!(ts.isVariableDeclarationList(d) && d.declarations.length === 1 && ts.isIdentifier(d.declarations[0].name))) throw this.err("use 'for (const k in obj)'", s);
    const obj = this.unwrap(this.expr(s.expression));
    if (obj.ty.k !== "dict") throw this.err("for-in is supported over Record objects", s);
    const seq = { e: "Builtin", ty: listOf(obj.ty.key), loc, name: "dict_keys", args: [obj] };
    const idx = `i$${++this.tmp}`;
    this.env[idx] = INT;
    const elem = this.bindLocal(d.declarations[0].name.text, obj.ty.key, s);
    const body = this.inner(s.statement);
    return [{ s: "ForEach", loc, elem, idx, seq, invariants: this.loopClauses(this.loopContracts(s)).invs, body, idx_visible: false }];
  }

  forOf(s, loc) {
    const cls = this.loopContracts(s);
    const d = s.initializer;
    if (!(ts.isVariableDeclarationList(d) && d.declarations.length === 1)) throw this.err("use 'for (const x of xs)'", s);
    if (!(d.flags & (ts.NodeFlags.Let | ts.NodeFlags.Const))) throw this.err("'var' is function-scoped and hoisted; use let or const", s);
    let seq = this.unwrap(this.expr(s.expression));
    const pat = d.declarations[0].name;
    // for (const [k, v] of map / map.entries() / Object.entries(rec))
    let dictSrc = null;
    const ex = s.expression;
    if (seq.ty.k === "dict") dictSrc = seq;
    else if (ts.isCallExpression(ex) && ts.isPropertyAccessExpression(ex.expression) && ex.expression.name.text === "entries" && !ex.arguments.length) {
      const m = this.unwrap(this.expr(ex.expression.expression));
      if (m.ty.k === "dict") dictSrc = m;
    } else if (ts.isCallExpression(ex) && ts.isPropertyAccessExpression(ex.expression) && ts.isIdentifier(ex.expression.expression) && ex.expression.expression.text === "Object" && ex.expression.name.text === "entries" && ex.arguments.length === 1) {
      const m = this.unwrap(this.expr(ex.arguments[0]));
      if (m.ty.k === "dict") dictSrc = m;
    }
    if (dictSrc && ts.isArrayBindingPattern(pat) && pat.elements.length === 2 && pat.elements.every((e) => ts.isBindingElement(e) && ts.isIdentifier(e.name))) {
      const keys = { e: "Builtin", ty: listOf(dictSrc.ty.key), loc, name: "dict_keys", args: [dictSrc] };
      const idx = `i$${++this.tmp}`;
      this.env[idx] = INT;
      const kname = this.bindLocal(pat.elements[0].name.text, dictSrc.ty.key, s);
      const vname = this.bindLocal(pat.elements[1].name.text, dictSrc.ty.val, s);
      const pre = [{ s: "Assign", loc, name: vname, value: { e: "Index", ty: dictSrc.ty.val, loc, seq: dictSrc, idx: { e: "Var", ty: dictSrc.ty.key, loc, name: kname }, wrap: false } }];
      const body = pre.concat(this.inner(s.statement));
      const { invs } = this.loopClauses(cls);
      return [{ s: "ForEach", loc, elem: kname, idx, seq: keys, invariants: invs, body, idx_visible: false }];
    }
    if (seq.ty.k === "dict") throw this.err("iterate a Map with 'for (const [k, v] of m)'", s);
    if (!ts.isIdentifier(pat)) {
      // for (const [a, b] of xs) / for (const { a } of xs): each element destructured
      if (seq.ty.k === "opaque") seq = this.coerce(seq, listOf(opaque("")));
      if (seq.ty.k !== "list") throw this.err("for-of needs an array", s);
      const idx = `i$${++this.tmp}`;
      this.env[idx] = INT;
      const elem = `elem$${++this.tmp}`;
      this.env[elem] = seq.ty.elem;
      const pre = [];
      this.destructureFrom(pat, { e: "Var", ty: seq.ty.elem, loc, name: elem }, s, loc, true, pre);
      const body = pre.concat(this.inner(s.statement));
      const { invs } = this.loopClauses(cls);
      return [{ s: "ForEach", loc, elem, idx, seq, invariants: invs, body, idx_visible: false }];
    }
    if (seq.ty.k === "opaque") seq = this.coerce(seq, listOf(opaque("")));
    if (seq.ty.k === "str") throw this.err("iterating over a string's characters is not supported", s);
    if (seq.ty.k !== "list") throw this.err("for-of needs an array", s);
    let index = null;
    for (const cl of cls) if (cl.keyword === "index") index = cl.payload.trim();
    if (index && (this.resolve(index) !== null || this.srcNames.has(index))) throw this.err(`'@index ${index}' names an existing variable; pick a fresh name`, s);
    const idx = index ? this.bindLocal(index, INT, s) : `i$${++this.tmp}`;
    if (!index) this.env[idx] = INT;
    const elem = this.bindLocal(pat.text, seq.ty.elem, s);
    const body = this.inner(s.statement);
    const { invs, dec } = this.loopClauses(cls);
    if (dec) throw this.err("a for-of loop terminates by construction; remove '@decreases'", s);
    return [{ s: "ForEach", loc, elem, idx, seq, invariants: invs, body, idx_visible: !!index }];
  }

  forStmt(s, loc) {
    const K = ts.SyntaxKind;
    const cls = this.loopContracts(s);
    const init = s.initializer, cond = s.condition, inc = s.incrementor;
    // Canonical counted loop: for (let i = lo; i < hi; i++) over integers,
    // with i untouched by the body  ==>  ForRange. JavaScript re-evaluates
    // `hi` every iteration, so the IR marks it and the verifier requires
    // that nothing the body does can change it.
    if (init && ts.isVariableDeclarationList(init) && init.flags & ts.NodeFlags.Let && init.declarations.length === 1 && ts.isIdentifier(init.declarations[0].name) && init.declarations[0].initializer && !init.declarations[0].type && cond && inc && ts.isBinaryExpression(cond) && cond.operatorToken.kind === K.LessThanToken && ts.isIdentifier(cond.left) && cond.left.text === init.declarations[0].name.text) {
      const v = cond.left.text;
      const isInc =
        ((ts.isPostfixUnaryExpression(inc) || ts.isPrefixUnaryExpression(inc)) && inc.operator === K.PlusPlusToken && ts.isIdentifier(inc.operand) && inc.operand.text === v) ||
        (ts.isBinaryExpression(inc) && inc.operatorToken.kind === K.PlusEqualsToken && ts.isIdentifier(inc.left) && inc.left.text === v && ts.isNumericLiteral(inc.right) && inc.right.text === "1");
      const lo = isInc ? this.expr(init.declarations[0].initializer) : null;
      if (isInc && lo.ty.k === "int") {
        const irv = this.bindLocal(v, INT, s);
        let hi = this.expr(cond.right);
        if (hi.ty.k === "opaque") hi = this.coerce(hi, INT);  // xs.length of an untyped value: a count
        if (hi.ty.k === "int") {
          const body = this.inner(s.statement);
          if (!assigned(body).has(irv)) {
            const { invs, dec } = this.loopClauses(cls);
            if (dec) throw this.err("this counted loop terminates by construction; remove '@decreases'", s);
            return [{ s: "ForRange", loc, var: irv, lo, hi, invariants: invs, body, reeval: true }];
          }
          const { invs, dec } = this.loopClauses(cls);
          const c = this.cond(cond);
          const step = this.exprStatement(inc, inc);
          return [{ s: "Assign", loc, name: irv, value: lo }, { s: "While", loc, cond: c, invariants: invs, decreases: dec, body, step }];
        }
        throw this.err("the loop bound must be an integer", s);
      }
    }
    const out = [];
    if (init) {
      if (ts.isVariableDeclarationList(init)) out.push(...this.varDecls(init, s, loc));
      else out.push(...this.exprStatement(init, s));
    }
    const c = cond ? this.cond(cond) : { e: "Lit", ty: BOOL, loc, value: true };
    const body = this.inner(s.statement);
    const step = inc ? this.exprStatement(inc, s) : [];
    const { invs, dec } = this.loopClauses(cls);
    out.push({ s: "While", loc, cond: c, invariants: invs, decreases: dec, body, step });
    return out;
  }

  // -- expressions --------------------------------------------------------

  lookup(name, node) {
    if (this.bound && name in this.bound) return this.bound[name];
    const ir = this.resolve(name);
    if (ir !== null) return this.env[ir];
    throw this.err(`unknown name '${name}'`, this.nline(node));
  }

  irName(name) {
    if (this.bound && name in this.bound) return name;
    return this.resolve(name) ?? name;
  }

  // An expression used only for its truth value: JavaScript truthiness
  // applies to &&, || and ! operands here, and nowhere else.
  cond(n) {
    const K = ts.SyntaxKind;
    if (ts.isParenthesizedExpression(n)) return this.cond(n.expression);
    if (ts.isBinaryExpression(n) && (n.operatorToken.kind === K.AmpersandAmpersandToken || n.operatorToken.kind === K.BarBarToken)) {
      return { e: "Binary", ty: BOOL, loc: this.nloc(n), op: n.operatorToken.kind === K.AmpersandAmpersandToken ? "and" : "or", left: this.cond(n.left), right: this.cond(n.right) };
    }
    return this.truthy(this.expr(n), n);
  }

  truthy(e, node) {
    if (e.ty.k === "bool") return e;
    if (isNum(e.ty)) return { e: "Binary", ty: BOOL, loc: e.loc, op: "ne", left: e, right: { e: "Lit", ty: e.ty, loc: e.loc, value: 0 } };
    if (e.ty.k === "str") return { e: "Binary", ty: BOOL, loc: e.loc, op: "ne", left: e, right: { e: "Lit", ty: STR, loc: e.loc, value: "" } };
    if (e.ty.k === "option") {
      const present = { e: "Unary", ty: BOOL, loc: e.loc, op: "not", arg: { e: "Builtin", ty: BOOL, loc: e.loc, name: "is_none", args: [e] } };
      if (["class", "record", "enum", "list", "dict"].includes(e.ty.inner.k)) return present;
      return { e: "Binary", ty: BOOL, loc: e.loc, op: "and", left: present, right: this.truthy(this.unwrap(e), node) };
    }
    if (e.ty.k === "opaque") return this.opaqueOp("truthy", [e], BOOL, e.loc);
    if (e.ty.k === "enum") {
      // numeric enums: the member with value 0 is falsy
      const zero = e.ty.values.indexOf(0), empty = e.ty.values.indexOf("");
      const f = zero >= 0 ? zero : empty;
      if (f < 0) return { e: "Lit", ty: BOOL, loc: e.loc, value: true };
      return { e: "Binary", ty: BOOL, loc: e.loc, op: "ne", left: e, right: { e: "Lit", ty: e.ty, loc: e.loc, value: f } };
    }
    if (["class", "record", "list", "dict"].includes(e.ty.k)) return { e: "Lit", ty: BOOL, loc: e.loc, value: true };
    if (e.ty.k === "none") return { e: "Lit", ty: BOOL, loc: e.loc, value: false };
    throw this.err(`cannot use a ${tyStr(e.ty)} as a condition`, this.nline(node));
  }

  unwrap(e) {
    return e.ty.k === "option" ? { e: "Builtin", ty: e.ty.inner, loc: e.loc, name: "unwrap", args: [e] } : e;
  }

  opaqueOp(op, parts, ty, loc) {
    return { e: "Builtin", ty, loc, name: "opaque_op", args: [{ e: "Lit", ty: STR, loc, value: op }, ...parts] };
  }

  extern(name, args, ty, loc) {
    if (this.spec) throw this.err(`specifications cannot call unchecked code ('${name}')`, loc[0]);
    return { e: "Extern", ty: ty && ty.k !== "opaque" ? ty : opaque(`result of ${name}`), loc, name, args };
  }

  numPair(a, b, node) {
    if (!(isNum(a.ty) && isNum(b.ty))) throw this.err(`arithmetic on ${tyStr(a.ty)} and ${tyStr(b.ty)}`, this.nline(node));
    if (a.ty.k === "real" || b.ty.k === "real") return [this.coerce(a, REAL), this.coerce(b, REAL), REAL];
    return [a, b, INT];
  }

  arith(op, a, b, node) {
    const loc = this.nloc(node);
    a = this.unwrap(a);
    b = this.unwrap(b);
    if (a.ty.k === "opaque" || b.ty.k === "opaque") return this.opaqueOp(op, [a, b], op === "add" ? opaque("") : REAL, loc);
    if (op === "add" && (a.ty.k === "str" || b.ty.k === "str")) return { e: "Builtin", ty: STR, loc, name: "str_concat", args: [this.toStr(a, loc), this.toStr(b, loc)] };
    if (op === "rdiv") {
      const [x, y] = this.numPair(a, b, node);
      return { e: "Binary", ty: REAL, loc, op: "rdiv", left: this.coerce(x, REAL), right: this.coerce(y, REAL) };
    }
    const [x, y, t] = this.numPair(a, b, node);
    return { e: "Binary", ty: t, loc, op, left: x, right: y };
  }

  // String(x) / `${x}` / "a" + x, as JavaScript converts it.
  toStr(e, loc) {
    if (e.ty.k === "str") return e;
    if (e.ty.k === "int") return { e: "Builtin", ty: STR, loc, name: "str_of_int", args: [e] };
    if (e.ty.k === "enum") {
      const vals = e.ty.values;
      if (vals.every((v) => typeof v === "string")) return { e: "Builtin", ty: STR, loc, name: "enum_value", args: [e] };
    }
    const part = ["list", "dict", "option", "class", "record", "none"].includes(e.ty.k) ? this.coerce(e, opaque("")) : e;
    return { e: "Builtin", ty: STR, loc, name: "str_fn", args: [{ e: "Lit", ty: STR, loc, value: "String" }, part] };
  }

  index(n) {
    const i = this.expr(n);
    if (i.ty.k !== "int") throw this.err("array index must be an integer (telic could not prove this number is an integer)", this.nline(n));
    return i;
  }

  expr(n, expect = null) {
    const K = ts.SyntaxKind;
    const loc = this.nloc(n);
    if (ts.isParenthesizedExpression(n)) return this.expr(n.expression, expect);
    if (ts.isNumericLiteral(n)) {
      const txt = n.text;
      if (/^\d+$/.test(txt)) return { e: "Lit", ty: INT, loc, value: Number(txt) };
      const f = decimalFraction(txt);
      if (!f) throw this.err(`unsupported numeric literal ${txt}`, this.nline(n));
      if (f[1] === 1) return { e: "Lit", ty: INT, loc, value: f[0] };
      return { e: "Lit", ty: REAL, loc, value: null, frac: f };
    }
    if (n.kind === K.TrueKeyword || n.kind === K.FalseKeyword) return { e: "Lit", ty: BOOL, loc, value: n.kind === K.TrueKeyword };
    if (ts.isStringLiteral(n) || ts.isNoSubstitutionTemplateLiteral(n)) return { e: "Lit", ty: STR, loc, value: n.text };
    if (n.kind === K.ThisKeyword) {
      const t = this.selfTy();
      if (!t) throw this.err("'this' outside a method", this.nline(n));
      return { e: "Var", ty: t, loc, name: "self" };
    }
    if (n.kind === K.NullKeyword) return { e: "Lit", ty: expect && expect.k === "option" ? expect : NONE, loc, value: null };
    if (ts.isIdentifier(n)) {
      if (this.spec && n.text === "result" && this.resultTy && !(this.bound && "result" in this.bound)) {
        if (this.resultTy.k === "none") throw this.err("'result' used but the function returns nothing", this.nline(n));
        return { e: "Result", ty: this.resultTy, loc };
      }
      const local = (this.bound && n.text in this.bound) || this.resolve(n.text) !== null;
      if (!local) {
        if (n.text === "undefined") return { e: "Lit", ty: expect && expect.k === "option" ? expect : NONE, loc, value: null };
        if (n.text in this.ml.constants) return this.expr(this.ml.constants[n.text], expect);
        if (this.ml.enums[n.text] || this.ml.classes[n.text] || this.ml.sigs[n.text] || this.ml.globalsBound.has(n.text) || GLOBALS.has(n.text) || this.ml.imported[n.text] || this.ml.namespaces[n.text]) {
          if (this.spec) throw this.err(`'${n.text}' is not a value a specification can use`, this.nline(n));
          return this.extern(n.text, [], null, loc); // a module-level value: read fresh each time
        }
      }
      return { e: "Var", ty: this.lookup(n.text, n), loc, name: this.irName(n.text) };
    }
    if (ts.isTemplateExpression(n)) {
      let out = { e: "Lit", ty: STR, loc, value: n.head.text };
      for (const sp of n.templateSpans) {
        const v = this.toStr(this.expr(sp.expression), loc);
        out = { e: "Builtin", ty: STR, loc, name: "str_concat", args: [out, v] };
        if (sp.literal.text) out = { e: "Builtin", ty: STR, loc, name: "str_concat", args: [out, { e: "Lit", ty: STR, loc, value: sp.literal.text }] };
      }
      return out;
    }
    if (ts.isAwaitExpression(n)) {
      const inner = this.expr(n.expression, expect);
      return { e: "Builtin", ty: inner.ty, loc, name: "await", args: [inner] };
    }
    if (ts.isNonNullExpression(n)) {
      // `x!` claims x is present: telic proves it
      const x = this.expr(n.expression);
      return x.ty.k === "option" ? this.unwrap(x) : x.ty.k === "opaque" ? x : x;
    }
    if (ts.isAsExpression(n) || (ts.isSatisfiesExpression && ts.isSatisfiesExpression(n)) || ts.isTypeAssertionExpression?.(n)) {
      const x = this.expr(n.expression, expect);
      if (ts.isSatisfiesExpression && ts.isSatisfiesExpression(n)) return x;
      if (ts.isTypeReferenceNode(n.type) && ts.isIdentifier(n.type.typeName) && n.type.typeName.text === "const") return x;
      const t = this.ml.typeOf(n.type);
      if (tyEq(t, x.ty)) return x;
      if (x.ty.k === "opaque" || t.k === "opaque") return this.coerce(x, t); // listed as an assumption
      if (isNum(t) && isNum(x.ty)) return this.coerce(x, t);
      throw this.err(`'as ${tyStr(t)}' on a ${tyStr(x.ty)} hides a type change telic would have to trust`, this.nline(n));
    }
    if (ts.isTypeOfExpression(n)) return this.opaqueOp("typeof", [this.expr(n.expression)], STR, loc);
    if (ts.isVoidExpression(n)) return { e: "Lit", ty: NONE, loc, value: null };
    if (ts.isArrowFunction(n) || ts.isFunctionExpression(n)) {
      if (this.spec) throw this.err("functions are not values in specifications", this.nline(n));
      return this.opaqueOp("closure", [], opaque("closure"), loc);
    }
    if (ts.isNewExpression(n)) return this.newExpr(n, loc, expect);
    if (ts.isPrefixUnaryExpression(n)) {
      if (n.operator === K.ExclamationToken) return { e: "Unary", ty: BOOL, loc, op: "not", arg: this.cond(n.operand) };
      const a = this.unwrap(this.expr(n.operand));
      if (a.ty.k === "opaque") return this.opaqueOp("unary", [a], opaque(""), loc);
      if (n.operator === K.MinusToken) {
        if (!isNum(a.ty)) throw this.err(`cannot negate ${tyStr(a.ty)}`, this.nline(n));
        if (a.e === "Lit") return a.frac ? { ...a, loc, frac: [-a.frac[0], a.frac[1]] } : { ...a, loc, value: -a.value };
        return { e: "Unary", ty: a.ty, loc, op: "neg", arg: a };
      }
      if (n.operator === K.PlusToken) return a;
      throw this.err("unsupported unary operator", this.nline(n));
    }
    if (ts.isBinaryExpression(n)) return this.binary(n, loc);
    if (ts.isConditionalExpression(n)) {
      const c = this.cond(n.condition);
      let a = this.expr(n.whenTrue, expect), b = this.expr(n.whenFalse, expect);
      if (!tyEq(a.ty, b.ty)) {
        const j = this.join(a.ty, b.ty);
        if (j) [a, b] = [this.coerce(a, j), this.coerce(b, j)];
        else if (isNum(a.ty) && isNum(b.ty)) [a, b] = this.numPair(a, b, n);
        else throw this.err(`conditional branches have types ${tyStr(a.ty)} and ${tyStr(b.ty)}`, this.nline(n));
      }
      return { e: "Ite", ty: a.ty, loc, cond: c, then: a, orelse: b };
    }
    if (ts.isCallExpression(n)) return this.call(n, loc, expect);
    if (ts.isElementAccessExpression(n)) {
      let seq = this.expr(n.expression);
      if (n.questionDotToken && seq.ty.k === "option") return this.optionalChain(seq, (x) => this.elementOf(x, n, loc), loc);
      return this.elementOf(this.unwrap(seq), n, loc);
    }
    if (ts.isPropertyAccessExpression(n)) {
      const name = n.name.text;
      if (ts.isIdentifier(n.expression) && !((this.bound && n.expression.text in this.bound) || this.resolve(n.expression.text) !== null)) {
        const base = n.expression.text;
        const et = this.ml.enums[base];
        if (et) {
          const i = et.members.indexOf(name);
          if (i < 0) throw this.err(`${base} has no member '${name}'`, this.nline(n));
          return { e: "Lit", ty: et, loc, value: i };
        }
        const ns = this.ml.namespaces[base];
        if (ns && ns.constants[name]) return this.expr(ns.constants[name], expect);
      }
      const obj = this.expr(n.expression);
      if (n.questionDotToken && obj.ty.k === "option") return this.optionalChain(obj, (x) => this.propertyOf(x, name, n, loc), loc);
      return this.propertyOf(this.unwrap(obj), name, n, loc);
    }
    if (ts.isJsxElement(n) || ts.isJsxSelfClosingElement(n) || ts.isJsxFragment(n)) {
      // a React element: built by the runtime; the expressions embedded in it are evaluated (and checked)
      if (this.spec) throw this.err("JSX is not supported in specifications", this.nline(n));
      const parts = [];
      const visit = (x) => {
        if (ts.isJsxExpression(x)) {
          if (x.expression) parts.push(this.expr(x.expression));
          return;
        }
        if (ts.isJsxSpreadAttribute(x)) {
          parts.push(this.expr(x.expression));
          return;
        }
        ts.forEachChild(x, visit);
      };
      ts.forEachChild(n, visit);
      return this.opaqueOp("jsx", parts.map((x) => (x.ty.k === "opaque" ? x : this.coerce(x, opaque("")))), opaque("React element"), loc);
    }
    if (n.kind === ts.SyntaxKind.RegularExpressionLiteral) return this.opaqueOp("regexp", [{ e: "Lit", ty: STR, loc, value: n.text }], opaque("RegExp"), loc);
    if (ts.isArrayLiteralExpression(n) && n.elements.some((e) => ts.isSpreadElement(e))) {
      if (this.spec) throw this.err("spread is not supported in specifications", this.nline(n));
      const parts = n.elements.map((e) => this.expr(ts.isSpreadElement(e) ? e.expression : e));
      return this.coerce(this.opaqueOp("array", parts.map((x) => (["list", "dict", "class", "option", "record"].includes(x.ty.k) ? this.coerce(x, opaque("")) : x)), opaque("array"), loc), expect && expect.k === "list" ? expect : listOf(opaque("")));
    }
    if (ts.isArrayLiteralExpression(n)) {
      const elemExpect = expect && expect.k === "list" ? expect.elem : null;
      let elems = n.elements.map((e) => this.expr(e, elemExpect));
      if (!elems.length) return { e: "ListLit", ty: expect && expect.k === "list" ? expect : listOf(NONE), loc, elems: [] };
      let t = elemExpect || elems[0].ty;
      if (elems.some((e) => e.ty.k === "real") && elems.every((e) => isNum(e.ty))) t = REAL;
      elems = elems.map((e) => this.coerce(e, t));
      if (elems.some((e) => !tyEq(e.ty, t))) throw this.err("array elements must all have one type", this.nline(n));
      return { e: "ListLit", ty: listOf(t), loc, elems };
    }
    if (ts.isObjectLiteralExpression(n) && expect && expect.k === "dict") {
      const args = [];
      for (const p of n.properties) {
        if (!ts.isPropertyAssignment(p) || !(ts.isIdentifier(p.name) || ts.isStringLiteral(p.name) || ts.isNumericLiteral(p.name))) throw this.err("unsupported entry in a dictionary literal", this.nline(p));
        const key = ts.isNumericLiteral(p.name) ? { e: "Lit", ty: expect.key, loc, value: Number(p.name.text) } : { e: "Lit", ty: STR, loc, value: p.name.text };
        args.push(this.coerce(key, expect.key), this.coerce(this.expr(p.initializer, expect.val), expect.val));
      }
      return { e: "Builtin", ty: expect, loc, name: "dict_lit", args };
    }
    if (ts.isObjectLiteralExpression(n) && (!expect || expect.k !== "record")) {
      if (this.spec) throw this.err("object literals need a known record type here", this.nline(n));
      const parts = [];
      for (const p of n.properties) {
        if (ts.isPropertyAssignment(p)) parts.push(this.expr(p.initializer));
        else if (ts.isShorthandPropertyAssignment(p)) parts.push(this.expr(p.name));
        else if (ts.isSpreadAssignment(p)) parts.push(this.expr(p.expression));
      }
      return this.opaqueOp("object", parts.map((x) => (["list", "dict", "class", "option", "record"].includes(x.ty.k) ? this.coerce(x, opaque("")) : x)), opaque("object literal"), loc);
    }
    if (ts.isObjectLiteralExpression(n) && n.properties.some((p) => !(ts.isPropertyAssignment(p) && ts.isIdentifier(p.name)) && !ts.isShorthandPropertyAssignment(p))) {
      // {...base, k: v}, computed keys, methods: built by the runtime; its fields have their declared types
      if (this.spec) throw this.err("object literals with spreads are not supported in specifications", this.nline(n));
      const parts = n.properties.map((p) => (ts.isPropertyAssignment(p) ? this.expr(p.initializer) : ts.isShorthandPropertyAssignment(p) ? this.expr(p.name) : ts.isSpreadAssignment(p) ? this.expr(p.expression) : null)).filter((x) => x);
      return this.coerce(this.opaqueOp("object", parts.map((x) => (x.ty.k === "opaque" ? x : this.coerce(x, opaque("")))), opaque("object literal"), loc), expect);
    }
    if (ts.isObjectLiteralExpression(n)) {
      if (!expect || expect.k !== "record") throw this.err("object literals need a known record type here (annotate the variable)", this.nline(n));
      const vals = {};
      for (const p of n.properties) {
        if (ts.isPropertyAssignment(p) && ts.isIdentifier(p.name)) {
          const ft = expect.fields.find((f) => f[0] === p.name.text);
          if (!ft) throw this.err(`${expect.name} has no field '${p.name.text}'`, this.nline(p));
          vals[p.name.text] = this.coerce(this.expr(p.initializer, ft[1]), ft[1]);
        } else if (ts.isShorthandPropertyAssignment(p)) {
          const ft = expect.fields.find((f) => f[0] === p.name.text);
          if (!ft) throw this.err(`${expect.name} has no field '${p.name.text}'`, this.nline(p));
          vals[p.name.text] = this.coerce({ e: "Var", ty: this.lookup(p.name.text, p), loc, name: this.irName(p.name.text) }, ft[1]);
        } else throw this.err("unsupported object literal member", this.nline(p));
      }
      for (const f of expect.fields) if (!(f[0] in vals) && f[1].k === "option") vals[f[0]] = { e: "Lit", ty: f[1], loc, value: null };  // optional fields left out are undefined
      const missing = expect.fields.filter((f) => !(f[0] in vals)).map((f) => f[0]);
      if (missing.length) throw this.err(`${expect.name} literal is missing ${missing.join(", ")}`, this.nline(n));
      return { e: "RecordLit", ty: expect, loc, fields: expect.fields.map((f) => [f[0], vals[f[0]]]) };
    }
    throw this.err(`unsupported expression: ${K[n.kind]}`, this.nline(n));
  }

  join(a, b) {
    if (a.k === "opaque" || b.k === "opaque") return opaque("");
    if (a.k === "none" && b.k !== "none") return optionOf(b);
    if (b.k === "none" && a.k !== "none") return optionOf(a);
    if (a.k === "option" && (tyEq(a.inner, b) || b.k === "none")) return a;
    if (b.k === "option" && (tyEq(b.inner, a) || a.k === "none")) return b;
    return null;
  }

  optionalChain(obj, f, loc) {
    // x?.p: undefined when x is absent, else x.p (as an optional)
    const inner = f(this.unwrap(obj));
    const rt = optionOf(inner.ty.k === "option" ? inner.ty.inner : inner.ty);
    if (rt.k === "opaque") return this.coerce(inner, rt);
    return { e: "Ite", ty: rt, loc, cond: { e: "Builtin", ty: BOOL, loc, name: "is_none", args: [obj] }, then: { e: "Lit", ty: rt, loc, value: null }, orelse: this.coerce(inner, rt) };
  }

  propertyOf(obj, name, n, loc) {
    const t = obj.ty;
    if (t.k === "list" && name === "length") return { e: "Builtin", ty: INT, loc, name: "len", args: [obj] };
    if (t.k === "str" && name === "length") return { e: "Builtin", ty: INT, loc, name: "str_len", args: [obj] };
    if (t.k === "dict" && name === "size") return this.opaqueOp("len", [obj], INT, loc);
    if (t.k === "record") {
      const f = t.fields.find((x) => x[0] === name);
      if (!f) throw this.err(`${t.name} has no field '${name}'`, this.nline(n));
      return { e: "Field", ty: f[1], loc, obj, name };
    }
    if (t.k === "class") {
      const c = this.ml.classes[t.name];
      const key = `${t.name}.${name}`;
      if (c && c.props.has(key)) return this.callSig(key, [obj], [], n, loc);
      const f = c && c.fields.find((x) => x[0] === name);
      if (!f) throw this.err(`${t.name} has no field '${name}'`, this.nline(n));
      return { e: "Field", ty: f[1], loc, obj, name };
    }
    if (t.k === "opaque") return this.opaqueOp(`attr.${name}`, [obj], opaque(""), loc);
    if (t.k === "dict" && t.js === "object") return this.elementOfDict(obj, { e: "Lit", ty: STR, loc, value: name }, loc);
    throw this.err(`unsupported property '.${name}' on ${tyStr(t)}`, this.nline(n));
  }

  elementOf(seq, n, loc) {
    const t = seq.ty;
    if (t.k === "list") return { e: "Index", ty: t.elem, loc, seq, idx: this.index(n.argumentExpression), wrap: false };
    if (t.k === "dict") return this.elementOfDict(seq, this.expr(n.argumentExpression), loc);
    if (t.k === "str") {
      const i = this.index(n.argumentExpression);
      return { e: "Builtin", ty: STR, loc, name: "str_index", args: [seq, i] };
    }
    if (t.k === "opaque") return this.opaqueOp("getitem", [seq, this.expr(n.argumentExpression)], opaque(""), loc);
    throw this.err(`cannot index a ${tyStr(t)}`, this.nline(n));
  }

  elementOfDict(d, k, loc) {
    const key = this.coerce(k, d.ty.key);
    return { e: "Index", ty: d.ty.val, loc, seq: d, idx: key, wrap: false };
  }

  newExpr(n, loc, expect) {
    const args = n.arguments || [];
    if (ts.isIdentifier(n.expression)) {
      const name = n.expression.text;
      if (name === "Map" && this.resolve(name) === null) {
        if (args.length) return this.extern("new Map", args.map((a) => this.expr(a)), expect, loc);
        let t = expect && expect.k === "dict" ? expect : null;
        if (!t && n.typeArguments && n.typeArguments.length === 2) {
          const k = this.ml.typeOf(n.typeArguments[0]), v = this.ml.typeOf(n.typeArguments[1]);
          t = ["int", "real", "str", "bool"].includes(k.k) && !["list", "dict", "option"].includes(v.k) ? { k: "dict", key: k, val: v, js: "map" } : null;
          if (!t) return this.extern("new Map", [], opaque("Map"), loc);
        }
        return { e: "Builtin", ty: t || { k: "dict", key: NONE, val: NONE, js: "map" }, loc, name: "dict_lit", args: [] };
      }
      const c = this.ml.classes[name];
      if (c && this.resolve(name) === null) {
        if (this.spec) throw this.err("specifications cannot create objects", this.nline(n));
        const key = `${name}.__init__`;
        const sig = this.ml.sigs[key];
        const bound = sig ? this.bindArgs(key, sig, sig.params.slice(1), args, n) : [];
        return { e: "New", ty: classOf(name), loc, cls: name, args: bound };
      }
    }
    return this.extern(`new ${n.expression.getText(this.ml.sf)}`, args.map((a) => this.expr(a)), expect, loc);
  }

  binary(n, loc) {
    const K = ts.SyntaxKind;
    const k = n.operatorToken.kind;
    if (k === K.QuestionQuestionToken) {
      const a = this.expr(n.left);
      if (a.ty.k === "none") return this.expr(n.right);
      if (a.ty.k === "opaque") return this.opaqueOp("??", [a, this.expr(n.right)], opaque(""), loc);
      if (a.ty.k !== "option") return a; // never nullish: the right side is not evaluated
      const b = this.expr(n.right, a.ty.inner);
      let rt;
      if (b.ty.k === "none" || b.ty.k === "option") rt = a.ty;
      else if (tyEq(b.ty, a.ty.inner)) rt = a.ty.inner;
      else if (isNum(b.ty) && isNum(a.ty.inner)) rt = REAL;
      else if (b.ty.k === "opaque") rt = opaque("");
      else throw this.err(`'??' mixes ${tyStr(a.ty)} and ${tyStr(b.ty)}`, this.nline(n));
      return { e: "Ite", ty: rt, loc, cond: { e: "Builtin", ty: BOOL, loc, name: "is_none", args: [a] }, then: this.coerce(b, rt), orelse: this.coerce(this.unwrap(a), rt) };
    }
    if (k === K.AmpersandAmpersandToken || k === K.BarBarToken) {
      // As a value, `a || b` is one of its operands, not a boolean.
      const a = this.expr(n.left), b = this.expr(n.right);
      if (a.ty.k === "bool" && b.ty.k === "bool") return { e: "Binary", ty: BOOL, loc, op: k === K.AmpersandAmpersandToken ? "and" : "or", left: a, right: b };
      if (a.ty.k === "opaque" || b.ty.k === "opaque") return this.opaqueOp(k === K.BarBarToken ? "||" : "&&", [a, b], opaque(""), loc);
      if (k === K.BarBarToken) {
        const base = a.ty.k === "option" ? a.ty.inner : a.ty;
        const j = tyEq(base, b.ty) ? base : isNum(base) && isNum(b.ty) ? REAL : this.join(base, b.ty);
        if (j) return { e: "Ite", ty: j, loc, cond: this.truthy(a, n.left), then: this.coerce(this.unwrap(a), j), orelse: this.coerce(b, j) };
      }
      throw this.err(`'${k === K.BarBarToken ? "||" : "&&"}' on ${tyStr(a.ty)} and ${tyStr(b.ty)} returns an operand, not a boolean; compare explicitly`, this.nline(n));
    }
    if (k === K.InKeyword) {
      const d = this.unwrap(this.expr(n.right));
      if (d.ty.k === "dict") return { e: "Builtin", ty: BOOL, loc, name: "dict_has", args: [d, this.coerce(this.expr(n.left), d.ty.key)] };
      return this.opaqueOp("in", [this.expr(n.left), this.coerce(d, opaque(""))], BOOL, loc);
    }
    if (k === K.InstanceOfKeyword) return this.opaqueOp("instanceof", [this.coerce(this.expr(n.left), opaque("")), { e: "Lit", ty: STR, loc, value: n.right.getText(this.spec ? this.specSf : this.ml.sf) }], BOOL, loc);
    const cmp = { [K.LessThanToken]: "lt", [K.LessThanEqualsToken]: "le", [K.GreaterThanToken]: "gt", [K.GreaterThanEqualsToken]: "ge", [K.EqualsEqualsEqualsToken]: "eq", [K.ExclamationEqualsEqualsToken]: "ne", [K.EqualsEqualsToken]: "eq", [K.ExclamationEqualsToken]: "ne" };
    if (cmp[k]) {
      let a = this.expr(n.left), b = this.expr(n.right);
      const eqop = cmp[k] === "eq" || cmp[k] === "ne";
      if (eqop && (a.ty.k === "none" || b.ty.k === "none")) {
        const other = a.ty.k === "none" ? b : a;
        let c;
        if (other.ty.k === "none") c = { e: "Lit", ty: BOOL, loc, value: true };
        else if (other.ty.k === "option") c = { e: "Builtin", ty: BOOL, loc, name: "is_none", args: [other] };
        else if (other.ty.k === "opaque") c = this.opaqueOp("is_nullish", [other], BOOL, loc);
        else c = { e: "Lit", ty: BOOL, loc, value: false }; // a non-optional value is never null/undefined
        return cmp[k] === "eq" ? c : { e: "Unary", ty: BOOL, loc, op: "not", arg: c };
      }
      if (a.ty.k === "opaque" || b.ty.k === "opaque") return this.opaqueOp(`cmp.${cmp[k]}`, [a, b], BOOL, loc);
      if (eqop && (a.ty.k === "option" || b.ty.k === "option")) {
        const j = this.join(a.ty, b.ty) || (isNum(a.ty.inner || a.ty) && isNum(b.ty.inner || b.ty) ? optionOf(REAL) : null);
        if (!j) throw this.err(`comparing ${tyStr(a.ty)} with ${tyStr(b.ty)}`, this.nline(n));
        return { e: "Binary", ty: BOOL, loc, op: cmp[k], left: this.coerce(a, j), right: this.coerce(b, j) };
      }
      if (!eqop) {
        a = this.unwrap(a);
        b = this.unwrap(b);
      }
      if (!eqop && a.ty.k === "str" && b.ty.k === "str") {
        const [x, y] = cmp[k] === "lt" || cmp[k] === "le" ? [a, b] : [b, a];
        return { e: "Builtin", ty: BOOL, loc, name: cmp[k] === "lt" || cmp[k] === "gt" ? "str_lt" : "str_le", args: [x, y] };
      }
      if (!eqop && a.ty.k === "enum") return this.opaqueOp(`cmp.${cmp[k]}`, [a, b], BOOL, loc);
      if (eqop && a.ty.k === "class" && tyEq(a.ty, b.ty)) return { e: "Binary", ty: BOOL, loc, op: cmp[k], left: a, right: b }; // identity
      if (isNum(a.ty) && isNum(b.ty)) [a, b] = this.numPair(a, b, n);
      else if (!tyEq(a.ty, b.ty)) throw this.err(`comparing ${tyStr(a.ty)} with ${tyStr(b.ty)}`, this.nline(n));
      else if (!["eq", "ne"].includes(cmp[k]) && !isNum(a.ty)) throw this.err(`ordering comparison on ${tyStr(a.ty)} is not supported`, this.nline(n));
      else if (a.ty.k === "list" || a.ty.k === "record" || a.ty.k === "dict") throw this.err("=== on arrays/objects compares identity, not contents; compare fields explicitly", this.nline(n));
      return { e: "Binary", ty: BOOL, loc, op: cmp[k], left: a, right: b };
    }
    const ar = { [K.PlusToken]: "add", [K.MinusToken]: "sub", [K.AsteriskToken]: "mul", [K.SlashToken]: "rdiv", [K.PercentToken]: "tmod" };
    if (ar[k]) return this.arith(ar[k], this.expr(n.left), this.expr(n.right), n);
    if ([K.AmpersandToken, K.BarToken, K.CaretToken, K.LessThanLessThanToken, K.GreaterThanGreaterThanToken, K.GreaterThanGreaterThanGreaterThanToken].includes(k) && !this.spec) return this.opaqueOp("bitwise", [this.expr(n.left), this.expr(n.right)], REAL, loc);
    if (k === K.AsteriskAsteriskToken && ts.isNumericLiteral(n.right) && /^[0-4]$/.test(n.right.text)) {
      const a = this.expr(n.left);
      const p = Number(n.right.text);
      if (p === 0) return { e: "Lit", ty: a.ty, loc, value: 1 };
      let out = a;
      for (let i = 1; i < p; i++) out = { e: "Binary", ty: a.ty, loc, op: "mul", left: out, right: a };
      return out;
    }
    if (k === K.AsteriskAsteriskToken && !this.spec) return this.opaqueOp("pow", [this.expr(n.left), this.expr(n.right)], REAL, loc);
    throw this.err(`unsupported operator '${n.operatorToken.getText(this.spec ? this.specSf : this.ml.sf)}'`, this.nline(n));
  }

  lambda(fnNode, params) {
    // (x, i) => body  or  x => body ; returns lowered body with bindings
    if (!(ts.isArrowFunction(fnNode) || ts.isFunctionExpression(fnNode))) throw this.err("expected an arrow function", this.nline(fnNode));
    if (fnNode.parameters.length > params.length) throw this.err("too many lambda parameters", this.nline(fnNode));
    const saved = this.bound;
    this.bound = { ...(this.bound || {}) };
    const names = [];
    fnNode.parameters.forEach((p, i) => {
      if (!ts.isIdentifier(p.name)) throw this.err("lambda parameters must be names", this.nline(p));
      this.bound[p.name.text] = params[i].ty;
      names.push(p.name.text);
    });
    try {
      let body = fnNode.body;
      if (ts.isBlock(body)) {
        if (body.statements.length === 1 && ts.isReturnStatement(body.statements[0]) && body.statements[0].expression) body = body.statements[0].expression;
        else throw this.err("lambda bodies must be a single expression", this.nline(fnNode));
      }
      return { names, body: this.expr(body) };
    } finally {
      this.bound = saved;
    }
  }

  call(n, loc, expect) {
    const c = n.expression;
    const args = n.arguments;
    if (ts.isPropertyAccessExpression(c)) {
      const m = c.name.text;
      if (ts.isIdentifier(c.expression) && c.expression.text === "Math") {
        if (["floor", "ceil", "trunc", "round"].includes(m)) {
          if (args.length !== 1) throw this.err(`Math.${m} takes one argument`, this.nline(n));
          // Math.floor(a / b) on integers is floor division.
          const a0 = args[0];
          const inner = ts.isParenthesizedExpression(a0) ? a0.expression : a0;
          if (m === "floor" && ts.isBinaryExpression(inner) && inner.operatorToken.kind === ts.SyntaxKind.SlashToken) {
            const l = this.expr(inner.left), r = this.expr(inner.right);
            if (l.ty.k === "int" && r.ty.k === "int") return { e: "Binary", ty: INT, loc, op: "floordiv", left: l, right: r };
          }
          const x = this.expr(a0);
          if (x.ty.k === "int") return x;
          if (x.ty.k !== "real") throw this.err(`Math.${m} needs a number`, this.nline(n));
          return { e: "Builtin", ty: INT, loc, name: m === "round" ? "round_up" : m, args: [x] };
        }
        if (["abs", "min", "max"].includes(m) && args.some((a) => this.expr(a).ty.k === "opaque")) return this.opaqueOp(`Math.${m}`, args.map((a) => this.expr(a)), opaque(""), loc);
        if (m === "abs") {
          const x = this.expr(args[0]);
          if (!isNum(x.ty)) throw this.err("Math.abs needs a number", this.nline(n));
          return { e: "Builtin", ty: x.ty, loc, name: "abs", args: [x] };
        }
        if (m === "min" || m === "max") {
          let xs = args.map((a) => this.unwrap(this.expr(a)));
          if (xs.length < 2 || !xs.every((x) => isNum(x.ty))) return this.extern(`Math.${m}`, xs, REAL, loc);
          const t = xs.some((x) => x.ty.k === "real") ? REAL : INT;
          return { e: "Builtin", ty: t, loc, name: m, args: xs.map((x) => this.coerce(x, t)) };
        }
        return this.extern(`Math.${m}`, args.map((a) => this.expr(a)), REAL, loc);
      }
      if (ts.isIdentifier(c.expression) && c.expression.text === "Number" && (m === "isInteger" || m === "isSafeInteger")) {
        const x = this.expr(args[0]);
        if (!isNum(x.ty)) throw this.err(`Number.${m} needs a number`, this.nline(n));
        let out = x.ty.k === "int" ? { e: "Lit", ty: BOOL, loc, value: true } : { e: "Builtin", ty: BOOL, loc, name: "is_int", args: [x] };
        if (m === "isSafeInteger") {
          const lim = { e: "Lit", ty: x.ty, loc, value: 9007199254740991 };
          const neg = { e: "Lit", ty: x.ty, loc, value: -9007199254740991 };
          out = { e: "Binary", ty: BOOL, loc, op: "and", left: out, right: { e: "Binary", ty: BOOL, loc, op: "and", left: { e: "Binary", ty: BOOL, loc, op: "le", left: neg, right: x }, right: { e: "Binary", ty: BOOL, loc, op: "le", left: x, right: lim } } };
        }
        return out;
      }
      if (ts.isIdentifier(c.expression) && c.expression.text === "console") throw this.err("console.* has no value", this.nline(n));
      if (ts.isIdentifier(c.expression) && this.resolve(c.expression.text) === null && !(this.bound && c.expression.text in this.bound)) {
        const base = c.expression.text;
        const key = `${base}.${m}`;
        if (this.ml.classes[base] && this.ml.sigs[key] && this.ml.sigs[key].isStatic) return this.callSig(key, [], args, n, loc);
        const ns = this.ml.namespaces[base];
        if (ns && ns.sigs[m] && !m.includes(".")) {
          if (!this.ml.sigs[key]) {
            this.ml.sigs[key] = ns.sigs[m];
            this.ml.module.imports[key] = [ns.rel, m];
          }
          return this.callSig(key, [], args, n, loc);
        }
        if (base === "Object" && ["keys", "values"].includes(m) && args.length === 1) {
          const d = this.unwrap(this.expr(args[0]));
          if (d.ty.k === "dict") return { e: "Builtin", ty: listOf(m === "keys" ? d.ty.key : d.ty.val), loc, name: m === "keys" ? "dict_keys" : "dict_values", args: [d] };
        }
        if (base === "Number" || base === "parseInt" || base === "parseFloat") return this.extern(key, args.map((a) => this.expr(a)), REAL, loc);
        if (this.ml.globalsBound.has(base) || GLOBALS.has(base) || this.ml.imported[base] || this.ml.namespaces[base] || this.ml.enums[base] || this.ml.classes[base]) {
          if (this.spec) throw this.err(`specifications cannot call unchecked code ('${key}')`, this.nline(n));
          return this.extern(key, args.map((a) => this.argValue(a)), expect, loc);
        }
      }
      // range(lo, hi).every(i => ...)   (spec helper)
      if ((m === "every" || m === "some") && ts.isCallExpression(c.expression) && ts.isIdentifier(c.expression.expression) && c.expression.expression.text === "range") {
        const ra = c.expression.arguments.map((a) => this.expr(a));
        if (ra.length !== 2 || !ra.every((x) => x.ty.k === "int")) throw this.err("range(lo, hi) needs two integers", this.nline(n));
        const lam = this.lambda(args[0], [{ ty: INT }]);
        const idx = lam.names[0] || `_${++this.tmp}`;
        return { e: "Quant", ty: BOOL, loc, kind: m === "every" ? "forall" : "exists", idx, lo: ra[0], hi: ra[1], body: this.truthy(lam.body, args[0]), elem: null, seq: null };
      }
      let obj = this.expr(c.expression);
      if (c.questionDotToken && obj.ty.k === "option") return this.optionalChain(obj, (x) => this.methodCall(x, m, n, loc, expect), loc);
      obj = this.unwrap(obj);
      if (obj.ty.k !== "list") return this.methodCall(obj, m, n, loc, expect);
      if (obj.ty.k === "list") {
        if (m === "every" || m === "some") {
          const lam = this.lambda(args[0], [{ ty: obj.ty.elem }, { ty: INT }]);
          const elem = lam.names[0] || `_e${++this.tmp}`;
          const idx = lam.names[1] || `${elem}$idx`;
          return { e: "Quant", ty: BOOL, loc, kind: m === "every" ? "forall" : "exists", idx, lo: { e: "Lit", ty: INT, loc, value: 0 }, hi: { e: "Builtin", ty: INT, loc, name: "len", args: [obj] }, body: this.truthy(lam.body, args[0]), elem, seq: obj };
        }
        if (m === "includes") {
          const v = this.coerce(this.expr(args[0]), obj.ty.elem);
          if (!tyEq(v.ty, obj.ty.elem)) throw this.err("includes() argument has the wrong type", this.nline(n));
          return { e: "Builtin", ty: BOOL, loc, name: "contains", args: [obj, v] };
        }
        if (m === "slice") {
          const none = { e: "Lit", ty: NONE, loc, value: null };
          const lo = args[0] ? this.index(args[0]) : none;
          const hi = args[1] ? this.index(args[1]) : none;
          return { e: "Builtin", ty: obj.ty, loc, name: "slice", args: [obj, lo, hi] };
        }
        if (m === "at") return { e: "Index", ty: obj.ty.elem, loc, seq: obj, idx: this.index(args[0]), wrap: true };
        if (m === "reduce" && args.length === 2 && isNum(obj.ty.elem)) {
          // xs.reduce((a, b) => a + b, 0)  ==>  sum(xs)
          const f = args[0];
          if ((ts.isArrowFunction(f) || ts.isFunctionExpression(f)) && f.parameters.length === 2 && ts.isIdentifier(f.parameters[0].name) && ts.isIdentifier(f.parameters[1].name)) {
            const a = f.parameters[0].name.text, b = f.parameters[1].name.text;
            let body = f.body;
            if (ts.isParenthesizedExpression(body)) body = body.expression;
            if (ts.isBinaryExpression(body) && body.operatorToken.kind === ts.SyntaxKind.PlusToken && ts.isIdentifier(body.left) && ts.isIdentifier(body.right) && ((body.left.text === a && body.right.text === b) || (body.left.text === b && body.right.text === a))) {
              const init = this.expr(args[1]);
              const s = { e: "Builtin", ty: obj.ty.elem, loc, name: "sum", args: [obj] };
              if (init.e === "Lit" && init.value === 0) return s;
              const [x, y, t] = this.numPair(init, s, n);
              return { e: "Binary", ty: t, loc, op: "add", left: x, right: y };
            }
          }
          throw this.err("only xs.reduce((a, b) => a + b, init) is supported", this.nline(n));
        }
        return this.listMethod(obj, m, n, loc, expect);
      }
      throw this.err(`unsupported method call .${m}()`, this.nline(n));
    }
    if (!ts.isIdentifier(c)) {
      if (this.spec) throw this.err("unsupported call", this.nline(n));
      return this.extern(c.getText(this.ml.sf).slice(0, 40), [this.coerce(this.expr(c), opaque("")), ...args.map((a) => this.argValue(a))], expect, loc);
    }
    const name = c.text;
    if (this.spec && name === "old") {
      if (!this.resultTy) throw this.err("old(...) is only allowed in '@ensures'", this.nline(n));
      const x = this.expr(args[0]);
      return { e: "Old", ty: x.ty, loc, expr: x };
    }
    if (this.spec && name === "implies") {
      const a = this.cond(args[0]), b = this.cond(args[1]);
      return { e: "Binary", ty: BOOL, loc, op: "implies", left: a, right: b };
    }
    if (this.spec && name === "sum") {
      const x = this.expr(args[0]);
      if (x.ty.k !== "list" || !isNum(x.ty.elem)) throw this.err("sum() needs an array of numbers", this.nline(n));
      return { e: "Builtin", ty: x.ty.elem, loc, name: "sum", args: [x] };
    }
    if (this.spec && name === "count") {
      const x = this.expr(args[0]);
      if (x.ty.k !== "list") throw this.err("count() needs an array", this.nline(n));
      return { e: "Builtin", ty: INT, loc, name: "count", args: [x, this.coerce(this.expr(args[1]), x.ty.elem)] };
    }
    const isLocal = this.resolve(name) !== null || (this.bound && name in this.bound);
    if (!isLocal && name === "String" && args.length === 1) return this.toStr(this.expr(args[0]), loc);
    if (!isLocal && name === "Boolean" && args.length === 1) return this.cond(args[0]);
    const sig = !isLocal ? this.ml.sigs[name] : null;
    if (sig && !sig.cls) return this.callSig(name, [], args, n, loc);
    if (this.spec) throw this.err(`call to '${name}', which telic cannot see (define it in a checked file with a contract)`, this.nline(n));
    if (isLocal && this.closures.has(name)) {
      // a local function: unchecked, and it may change what it captures
      const caps = [...this.closures.get(name)].map((x) => this.resolve(x)).filter((x) => x && x in this.env && ["list", "dict", "class", "opaque"].includes(this.env[x].k));
      for (const x of this.closures.get(name)) this.escaped.add(x);
      return this.extern(`local ${name}`, [...caps.map((x) => ({ e: "Var", ty: this.env[x], loc, name: x })), ...args.map((a) => this.argValue(a))], expect, loc);
    }
    return this.extern(name, [...(isLocal ? [this.coerce(this.expr(c), opaque(""))] : []), ...args.map((a) => this.argValue(a))], expect, loc);
  }

  // An argument handed to unchecked code: functions become opaque values.
  argValue(a) {
    if (ts.isSpreadElement(a)) return this.coerce(this.expr(a.expression), opaque(""));
    return this.expr(a);
  }

  callSig(key, pre, argNodes, n, loc) {
    const sig = this.ml.sigs[key];
    const bound = this.bindArgs(key, sig, sig.params.slice(pre.length), argNodes, n);
    return { e: "Call", ty: sig.ret, loc, func: key, args: [...pre, ...bound] };
  }

  // Match arguments to parameters: optional parameters may be omitted
  // (undefined), defaults fill in, extra arguments go to a rest parameter.
  bindArgs(key, sig, params, argNodes, n) {
    const out = [];
    let i = 0;
    for (const p of params) {
      if (sig.rest === p.name) {
        const extra = argNodes.slice(i).map((a) => this.argValue(a));
        out.push(this.opaqueOp("rest", extra.map((x) => (["list", "dict", "class", "option", "record"].includes(x.ty.k) ? this.coerce(x, opaque("")) : x)), opaque("...rest"), this.nloc(n)));
        i = argNodes.length;
        continue;
      }
      const a = argNodes[i++];
      let v;
      if (a === undefined) {
        if (p.name in (sig.defaults || {})) {
          const d = sig.defaults[p.name];
          v = d ? this.coerce(this.expr(d, p.ty), p.ty) : { e: "Extern", ty: p.ty, loc: this.nloc(n), name: `default of '${p.name}'`, args: [] };
        } else if (p.ty.k === "option" || p.ty.k === "opaque") v = this.coerce({ e: "Lit", ty: NONE, loc: this.nloc(n), value: null }, p.ty);
        else throw this.err(`'${key}' is missing argument '${p.name}'`, this.nline(n));
      } else v = this.coerce(this.expr(a, p.ty), p.ty);
      if (!tyEq(v.ty, p.ty) && !(p.ty.k === "list" && v.ty.k === "list" && v.ty.elem.k === "none") && !(p.ty.k === "dict" && v.ty.k === "dict" && v.ty.key.k === "none")) {
        if (p.ty.k === "int" && v.ty.k === "real") throw this.err(`argument '${p.name}' of '${key}' must be an integer; telic cannot show this number is one`, this.nline(n));
        throw this.err(`argument '${p.name}' of '${key}' expects ${tyStr(p.ty)}, got ${tyStr(v.ty)}`, this.nline(n));
      }
      out.push(v);
    }
    if (i < argNodes.length) throw this.err(`'${key}' takes ${params.length} arguments, got ${argNodes.length}`, this.nline(n));
    return out;
  }

  methodCall(obj, m, n, loc, expect) {
    const args = n.arguments;
    const t = obj.ty;
    if (t.k === "class") {
      const key = `${t.name}.${m}`;
      const sig = this.ml.sigs[key];
      if (!sig || sig.isStatic) throw this.err(`${t.name} has no checked method '${m}'`, this.nline(n));
      return this.callSig(key, [obj], args, n, loc);
    }
    if (t.k === "str") return this.strMethod(obj, m, n, loc, expect);
    if (t.k === "dict") return this.dictMethod(obj, m, n, loc, expect);
    if (t.k === "opaque" || t.k === "enum" || t.k === "record") {
      if (this.spec) throw this.err(`specifications cannot call unchecked code ('.${m}')`, this.nline(n));
      return this.extern(`${n.expression.expression.getText(this.ml.sf).slice(0, 30)}.${m}`, [this.coerce(obj, opaque("")), ...args.map((a) => this.argValue(a))], expect, loc);
    }
    throw this.err(`unsupported method call .${m}() on ${tyStr(t)}`, this.nline(n));
  }

  strMethod(s0, m, n, loc, expect) {
    const args = n.arguments.map((a) => this.expr(a));
    const lit = (v) => ({ e: "Lit", ty: STR, loc, value: v });
    const allStr = args.every((a) => a.ty.k === "str");
    if (m === "includes" && args.length === 1 && allStr) return { e: "Builtin", ty: BOOL, loc, name: "str_contains", args: [s0, args[0]] };
    if ((m === "startsWith" || m === "endsWith") && args.length === 1 && allStr) return { e: "Builtin", ty: BOOL, loc, name: m === "startsWith" ? "str_startswith" : "str_endswith", args: [s0, args[0]] };
    if (m === "indexOf" && args.length === 1 && allStr) return { e: "Builtin", ty: INT, loc, name: "str_find", args: [s0, args[0]] };
    if (m === "slice" && args.length <= 2 && args.every((a) => a.ty.k === "int")) {
      const none = { e: "Lit", ty: NONE, loc, value: null };
      return { e: "Builtin", ty: STR, loc, name: "str_slice", args: [s0, args[0] || none, args[1] || none] };
    }
    if (m === "toString" || m === "valueOf") return s0;
    if (["toLowerCase", "toUpperCase", "trim", "trimStart", "trimEnd", "padStart", "padEnd", "replace", "replaceAll", "repeat", "normalize", "concat", "substring", "substr", "charAt", "toLocaleLowerCase", "toLocaleUpperCase"].includes(m) && args.every((a) => ["str", "int", "real"].includes(a.ty.k))) {
      return { e: "Builtin", ty: STR, loc, name: "str_fn", args: [lit(m), s0, ...args] };
    }
    if (m === "split") return this.extern("String.split", [s0, ...args], listOf(STR), loc);
    return this.extern(`String.${m}`, [s0, ...args.map((a) => (["list", "dict", "class", "option", "record"].includes(a.ty.k) ? this.coerce(a, opaque("")) : a))], expect, loc);
  }

  dictMethod(d, m, n, loc, expect) {
    const args = n.arguments;
    const t = d.ty;
    if (m === "get" && args.length === 1) return { e: "Builtin", ty: optionOf(t.val), loc, name: "dict_get_opt", args: [d, this.coerce(this.expr(args[0]), t.key)] };
    if (m === "has" && args.length === 1) return { e: "Builtin", ty: BOOL, loc, name: "dict_has", args: [d, this.coerce(this.expr(args[0]), t.key)] };
    if (m === "keys" && !args.length) return { e: "Builtin", ty: listOf(t.key), loc, name: "dict_keys", args: [d] };
    if (m === "values" && !args.length) return { e: "Builtin", ty: listOf(t.val), loc, name: "dict_values", args: [d] };
    if (this.spec) throw this.err(`'.${m}()' is not supported in specifications`, this.nline(n));
    if (d.e !== "Var" && ["set", "delete", "clear"].includes(m)) throw this.err(`'.${m}()' on a map that is not a variable is not tracked`, this.nline(n));
    return this.extern(`Map.${m}`, [d, ...args.map((a) => this.argValue(a))], expect, loc);
  }

  listMethod(xs, m, n, loc, expect) {
    const args = n.arguments;
    const t = xs.ty;
    if ((m === "map" || m === "filter") && args.length === 1 && (ts.isArrowFunction(args[0]) || ts.isFunctionExpression(args[0])) && args[0].parameters.length === 1 && ts.isIdentifier(args[0].parameters[0].name)) {
      try {
        const lam = this.lambda(args[0], [{ ty: t.elem }]);
        const elem = lam.names[0];
        if (m === "map" && !["list", "dict"].includes(lam.body.ty.k)) return { e: "Builtin", ty: listOf(lam.body.ty), loc, name: "comp", args: [xs, { e: "Lit", ty: STR, loc, value: elem }, lam.body] };
        if (m === "filter") {
          const saved = this.bound;
          this.bound = { ...(this.bound || {}), [elem]: t.elem };
          try {
            const cond = this.truthy(lam.body, args[0]);
            return { e: "Builtin", ty: t, loc, name: "comp", args: [xs, { e: "Lit", ty: STR, loc, value: elem }, { e: "Var", ty: t.elem, loc, name: elem }, cond] };
          } finally {
            this.bound = saved;
          }
        }
      } catch (e) {
        if (!(e instanceof LowerError) || this.spec) throw e;
      }
    }
    if (this.spec) throw this.err(`array method .${m}() is not supported in specifications`, this.nline(n));
    const res = { find: optionOf(t.elem), pop: optionOf(t.elem), shift: optionOf(t.elem), indexOf: INT, findIndex: INT, lastIndexOf: INT, join: STR, concat: t, map: listOf(opaque("")), filter: t, flatMap: listOf(opaque("")), push: REAL, unshift: REAL, toString: STR }[m];
    if (["push", "pop", "shift", "unshift", "splice", "sort", "reverse", "fill", "copyWithin"].includes(m) && xs.e !== "Var") throw this.err(`'.${m}()' on an array that is not a variable is not tracked`, this.nline(n));
    // a non-mutating method leaves the array alone unless a callback mentions it
    const mentions = (a) => xs.e === "Var" && (() => { let hit = false; const v = (x) => { if (ts.isIdentifier(x) && this.resolve(x.text) === xs.name) hit = true; ts.forEachChild(x, v); }; v(a); return hit; })();
    const pure = !["push", "pop", "shift", "unshift", "splice", "sort", "reverse", "fill", "copyWithin"].includes(m) && !args.some(mentions);
    const recv = pure && xs.e === "Var" ? this.coerce(xs, opaque("")) : xs;
    const call = this.extern(`Array.${m}`, [recv, ...args.map((a) => this.argValue(a))], res || expect, loc);
    // whatever the callback does, map returns one element per element
    if (m === "map" && call.ty.k === "list") return { e: "Builtin", ty: call.ty, loc, name: "same_len", args: [xs, call] };
    return call;
  }
}

// ---------------------------------------------------------------------------
// Helpers

function safeType(ml, tn) {
  try {
    return ml.typeOf(tn);
  } catch {
    return null;
  }
}

function decimalFraction(txt) {
  const m = /^(\d*)\.?(\d*)(?:[eE]([+-]?\d+))?$/.exec(txt.replace(/_/g, ""));
  if (!m) return null;
  let num = BigInt((m[1] || "0") + (m[2] || ""));
  let den = 10n ** BigInt((m[2] || "").length);
  const exp = m[3] ? Number(m[3]) : 0;
  if (exp > 0) num *= 10n ** BigInt(exp);
  if (exp < 0) den *= 10n ** BigInt(-exp);
  const g = gcd(num, den);
  num /= g;
  den /= g;
  if (num > BigInt(Number.MAX_SAFE_INTEGER) || den > BigInt(Number.MAX_SAFE_INTEGER)) return null;
  return [Number(num), Number(den)];
}

function gcd(a, b) {
  while (b) [a, b] = [b, a % b];
  return a < 0n ? -a : a || 1n;
}

function staticType(fl, e, ints, params) {
  if (ts.isParenthesizedExpression(e)) return staticType(fl, e.expression, ints, params);
  if (ts.isIdentifier(e)) {
    if (params.has(e.text)) return params.get(e.text);
    if (ints.has(e.text)) return INT;
    return fl.env[e.text] || null;
  }
  return null;
}

function isIntExpr(fl, e, ints, params) {
  const K = ts.SyntaxKind;
  if (ts.isParenthesizedExpression(e)) return isIntExpr(fl, e.expression, ints, params);
  if (ts.isNumericLiteral(e)) return /^\d+$/.test(e.text) || (decimalFraction(e.text) || [0, 2])[1] === 1;
  if (ts.isIdentifier(e)) {
    if (params.has(e.text)) return params.get(e.text).k === "int";
    return ints.has(e.text);
  }
  if (ts.isPrefixUnaryExpression(e)) return (e.operator === K.MinusToken || e.operator === K.PlusToken) && isIntExpr(fl, e.operand, ints, params);
  if (ts.isBinaryExpression(e)) {
    const k = e.operatorToken.kind;
    if ([K.PlusToken, K.MinusToken, K.AsteriskToken, K.PercentToken].includes(k)) return isIntExpr(fl, e.left, ints, params) && isIntExpr(fl, e.right, ints, params);
    if (k === K.AsteriskAsteriskToken) return isIntExpr(fl, e.left, ints, params) && ts.isNumericLiteral(e.right);
    return false;
  }
  if (ts.isConditionalExpression(e)) return isIntExpr(fl, e.whenTrue, ints, params) && isIntExpr(fl, e.whenFalse, ints, params);
  if (ts.isPropertyAccessExpression(e) && e.name.text === "length") return true;
  if (ts.isElementAccessExpression(e)) {
    const t = staticType(fl, e.expression, ints, params);
    return !!(t && t.k === "list" && t.elem.k === "int");
  }
  if (ts.isPropertyAccessExpression(e) && ts.isIdentifier(e.expression)) {
    const t = staticType(fl, e.expression, ints, params);
    if (t && t.k === "record") {
      const f = t.fields.find((x) => x[0] === e.name.text);
      return !!(f && f[1].k === "int");
    }
    return false;
  }
  if (ts.isCallExpression(e)) {
    const c = e.expression;
    if (ts.isPropertyAccessExpression(c) && ts.isIdentifier(c.expression) && c.expression.text === "Math") {
      const m = c.name.text;
      if (["floor", "ceil", "trunc", "round"].includes(m)) return true;
      if (["abs", "min", "max"].includes(m)) return e.arguments.every((a) => isIntExpr(fl, a, ints, params));
      return false;
    }
    if (ts.isIdentifier(c) && fl.ml.sigs[c.text]) return fl.ml.sigs[c.text].ret.k === "int";
    if (ts.isPropertyAccessExpression(c) && c.name.text === "reduce") {
      const t = staticType(fl, c.expression, ints, params);
      return !!(t && t.k === "list" && t.elem.k === "int") && e.arguments.length === 2 && isIntExpr(fl, e.arguments[1], ints, params);
    }
  }
  return false;
}

function assigned(stmts) {
  const out = new Set();
  const walk = (ss) => {
    for (const s of ss) {
      if (["Assign", "IndexAssign", "Append"].includes(s.s)) out.add(s.name);
      if (s.s === "ForRange") out.add(s.var);
      if (s.s === "ForEach") {
        out.add(s.elem);
        out.add(s.idx);
      }
      for (const k of ["then", "orelse", "body", "step"]) if (Array.isArray(s[k])) walk(s[k]);
    }
  };
  walk(stmts);
  return out;
}

function varsIn(e) {
  const out = [];
  const walk = (x) => {
    if (!x || typeof x !== "object") return;
    if (x.e === "Var") out.push(x.name);
    for (const v of Object.values(x)) {
      if (Array.isArray(v)) v.forEach(walk);
      else if (v && typeof v === "object" && v.e) walk(v);
    }
  };
  walk(e);
  return out;
}

// ---------------------------------------------------------------------------

// Resolve `import ... from "./x"` to another module of this run.
function resolveImport(ml, spec, byFile) {
  if (!spec.startsWith(".")) return null;
  const base = path.resolve(path.dirname(ml.file), spec);
  for (const cand of [base, base + ".ts", base + ".tsx", path.join(base, "index.ts"), path.join(base, "index.tsx"), base.replace(/\.js$/, ".ts")]) {
    if (byFile.has(cand)) return byFile.get(cand);
  }
  return null;
}

function link(mls, byFile, stage) {
  for (const ml of mls) {
    for (const d of ml.importDecls) {
      const other = resolveImport(ml, d.spec, byFile);
      if (!other || other === ml) continue;
      if (stage === "names") {
        if (d.name === "*") {
          ml.namespaces[d.local] = other;
          continue;
        }
        if (other.enums[d.name]) ml.enums[d.local] = other.enums[d.name];
        else if (other.module.records[d.name]) ml.module.records[d.local] = other.module.records[d.name];
        else if (other.classes[d.name] && d.local === d.name) ml.classes[d.name] = other.classes[d.name];
        else if (d.name in other.constants) ml.constants[d.local] = other.constants[d.name];
        else if (other.aliases[d.name]) ml.aliases[d.local] = other.aliases[d.name];
        else ml.imported[d.local] = { mod: other, name: d.name };
        ml.globalsBound.delete(d.local);
        if (ml.imported[d.local] === undefined) delete ml.imported[d.local];
      } else if (stage === "signatures") {
        if (d.name !== "*" && other.sigs[d.name] && !other.sigs[d.name].cls) {
          ml.sigs[d.local] = other.sigs[d.name];
          ml.module.imports[d.local] = [other.rel, d.name];
          delete ml.imported[d.local];
        }
        if (other.classes[d.name] && ml.classes[d.name] === other.classes[d.name]) {
          for (const [k, sig] of Object.entries(other.sigs)) if (k.startsWith(d.name + ".")) ml.sigs[k] = sig;
        }
      }
    }
  }
}

function main() {
  const [root, ...files] = process.argv.slice(2);
  const mls = [];
  const byFile = new Map();
  for (const file of files) {
    const text = fs.readFileSync(file, "utf8");
    const sf = ts.createSourceFile(file, text, ts.ScriptTarget.Latest, true, file.endsWith("x") ? ts.ScriptKind.TSX : ts.ScriptKind.TS);
    const rel = path.relative(root, file);
    const ml = new ModuleLowerer(file, rel, sf);
    ml.gen = ml.phases();
    mls.push(ml);
    byFile.set(path.resolve(file), ml);
  }
  const advance = (to) => {
    for (const ml of mls) {
      if (ml.stage === "done") continue;
      try {
        for (;;) {
          const r = ml.gen.next();
          if (r.done) {
            ml.stage = "done";
            break;
          }
          if (r.value === to) {
            ml.stage = to;
            break;
          }
        }
      } catch (e) {
        ml.stage = "done";
        ml.module = { path: ml.rel, language: "typescript", source: ml.src, functions: [], intents: [], records: {}, classes: {}, imports: {}, problems: [[`internal error: ${e.message}`, e.line || 0]], notes: [], assumptions: JS_ASSUMPTIONS };
      }
    }
  };
  advance("names");
  link(mls, byFile, "names");
  advance("signatures");
  link(mls, byFile, "signatures");
  advance("done");
  const out = [];
  for (const ml of mls) {
    const mod = ml.module;
    const sf = ml.sf;
    if (sf.parseDiagnostics && sf.parseDiagnostics.length) {
      const d = sf.parseDiagnostics[0];
      const lc = sf.getLineAndCharacterOfPosition(d.start || 0);
      mod.problems.push([`syntax error: ${ts.flattenDiagnosticMessageText(d.messageText, " ")}`, lc.line + 1]);
    }
    mod.file = ml.file;
    out.push(mod);
  }
  process.stdout.write(JSON.stringify(out));
}

main();
