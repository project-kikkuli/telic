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
const tyEq = (a, b) => JSON.stringify(a) === JSON.stringify(b);
const isNum = (t) => t && (t.k === "int" || t.k === "real");
const tyStr = (t) => (t.k === "list" ? `${tyStr(t.elem)}[]` : t.k === "record" ? t.name : t.k === "real" ? "number" : t.k === "int" ? "int" : t.k);

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
    this.module = { path: rel, language: "typescript", source: sf.text, functions: [], intents: [], records: {}, problems: [], assumptions: JS_ASSUMPTIONS };
    this.aliases = {};
    this.sigs = {}; // name -> {params, ret, node}
  }

  line(node) {
    return this.sf.getLineAndCharacterOfPosition(node.getStart(this.sf)).line + 1;
  }
  loc(node) {
    const s = this.sf.getLineAndCharacterOfPosition(node.getStart(this.sf));
    const e = this.sf.getLineAndCharacterOfPosition(node.getEnd());
    return [s.line + 1, s.character, e.line === s.line ? e.character : 0];
  }

  run() {
    try {
      this.contracts = parseContractLines(collectComments(this.sf));
    } catch (e) {
      this.module.problems.push([e.message, e.line || 0]);
      return this.module;
    }
    // Records & aliases.
    for (const st of this.sf.statements) {
      if (ts.isInterfaceDeclaration(st)) this.record(st.name.text, st.members, st);
      else if (ts.isTypeAliasDeclaration(st)) {
        if (ts.isTypeLiteralNode(st.type)) this.record(st.name.text, st.type.members, st);
        else this.aliases[st.name.text] = st.type;
      }
    }
    // Function declarations (and `const f = (...) => ...`).
    const fns = [];
    const isAsync = (n) => !!(n.modifiers && n.modifiers.some((m) => m.kind === ts.SyntaxKind.AsyncKeyword)) || !!n.asteriskToken;
    for (const st of this.sf.statements) {
      if ((ts.isFunctionDeclaration(st) && isAsync(st)) || (ts.isVariableStatement(st) && st.declarationList.declarations.some((d) => d.initializer && (ts.isArrowFunction(d.initializer) || ts.isFunctionExpression(d.initializer)) && isAsync(d.initializer)))) continue;
      if (ts.isFunctionDeclaration(st) && st.name && st.body) fns.push({ name: st.name.text, node: st, exported: !!(ts.getCombinedModifierFlags(st) & ts.ModifierFlags.Export) });
      else if (ts.isVariableStatement(st) && st.declarationList.declarations.length === 1) {
        const d = st.declarationList.declarations[0];
        if (ts.isIdentifier(d.name) && d.initializer && (ts.isArrowFunction(d.initializer) || ts.isFunctionExpression(d.initializer)) && st.declarationList.flags & ts.NodeFlags.Const) {
          fns.push({ name: d.name.text, node: d.initializer, stmt: st, exported: !!(ts.getCombinedModifierFlags(st) & ts.ModifierFlags.Export) });
        }
      }
    }
    for (const f of fns) {
      try {
        this.sigs[f.name] = this.signature(f);
      } catch (e) {
        if (!(e instanceof LowerError)) throw e;
        this.module.problems.push([`${f.name}: ${e.message}`, e.line || this.line(f.node)]);
      }
    }
    this.inferIntegrality(fns);
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
      if (ts.isClassDeclaration(n) || ts.isClassExpression(n)) {
        const name = n.name ? n.name.text : "class";
        spans.push([n.getStart(this.sf), n.getEnd(), `methods are not checked yet (in '${name}'); telic checks top-level functions`]);
      } else if ((ts.isFunctionDeclaration(n) || ts.isArrowFunction(n) || ts.isFunctionExpression(n)) && n.modifiers && n.modifiers.some((m) => m.kind === ts.SyntaxKind.AsyncKeyword)) {
        spans.push([n.getFullStart(), n.getEnd(), "async functions are not checked yet"]);
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
    return this.module;
  }

  record(name, members, node) {
    const fields = [];
    for (const m of members) {
      if (!ts.isPropertySignature(m) || !m.type || !ts.isIdentifier(m.name) || m.questionToken) return;
      let t;
      try {
        t = this.typeOf(m.type);
      } catch {
        return;
      }
      if (t.k === "list") return;
      fields.push([m.name.text, t]);
    }
    this.module.records[name] = { k: "record", name, fields };
  }

  typeOf(tn, intHint = false) {
    if (!tn) throw new LowerError("missing type annotation");
    switch (tn.kind) {
      case ts.SyntaxKind.NumberKeyword:
        return intHint ? INT : REAL;
      case ts.SyntaxKind.BooleanKeyword:
        return BOOL;
      case ts.SyntaxKind.StringKeyword:
        return STR;
      case ts.SyntaxKind.VoidKeyword:
        return NONE;
    }
    if (ts.isArrayTypeNode(tn)) return listOf(this.typeOf(tn.elementType));
    if (ts.isTypeOperatorNode(tn) && tn.operator === ts.SyntaxKind.ReadonlyKeyword) return this.typeOf(tn.type, intHint);
    if (ts.isTypeReferenceNode(tn) && ts.isIdentifier(tn.typeName)) {
      const n = tn.typeName.text;
      if ((n === "Array" || n === "ReadonlyArray") && tn.typeArguments && tn.typeArguments.length === 1) return listOf(this.typeOf(tn.typeArguments[0]));
      if (["int", "Int", "integer", "Integer"].includes(n) && this.aliases[n]) return INT;
      if (this.module.records[n]) return this.module.records[n];
      if (this.aliases[n]) return this.typeOf(this.aliases[n], intHint);
      throw new LowerError(`unsupported type '${n}'`, this.line(tn));
    }
    if (ts.isParenthesizedTypeNode(tn)) return this.typeOf(tn.type, intHint);
    if (ts.isUnionTypeNode(tn) && tn.types.every((t) => ts.isLiteralTypeNode(t) && ts.isStringLiteral(t.literal))) return STR;
    throw new LowerError(`unsupported type '${tn.getText(this.sf)}'`, this.line(tn));
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
    const cls = this.functionContracts(f);
    // integrality hints from @requires: Number.isInteger(p) / isSafeInteger(p)
    const ints = new Set();
    for (const cl of cls) {
      if (cl.keyword !== "requires") continue;
      for (const m of cl.payload.matchAll(/Number\.is(?:Safe)?Integer\(\s*([A-Za-z_$][\w$]*)\s*\)/g)) ints.add(m[1]);
    }
    const params = [];
    for (const p of node.parameters) {
      if (!ts.isIdentifier(p.name)) throw new LowerError("destructured parameters are not supported", this.line(p));
      if (p.initializer || p.questionToken || p.dotDotDotToken) throw new LowerError("optional, default and rest parameters are not supported", this.line(p));
      if (!p.type) throw new LowerError(`parameter '${p.name.text}' needs a type annotation`, this.line(p));
      params.push({ name: p.name.text, ty: this.typeOf(p.type, ints.has(p.name.text)) });
    }
    let ret = NONE, retInferred = false;
    if (node.type) ret = this.typeOf(node.type);
    else if (node.body && !ts.isBlock(node.body)) retInferred = true;
    else retInferred = true;
    return { params, ret, retInferred, node, contracts: cls, intsFromContract: ints };
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
    this.sig = ml.sigs[f.name];
    this.env = {};
    this.probe = probe;
    this.tmp = 0;
    this.unsupported = [];
    this.intents = [];
    this.currentIntents = [];
    const start = (f.stmt || f.node).getStart(ml.sf), end = f.node.getEnd();
    this.localContracts = ml.contracts.filter((cl) => cl.pos >= start && cl.pos <= end);
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
    if (this.node.body) visit(this.node.body);
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
    const fn = {
      name: this.f.name,
      loc: ml.loc(this.f.stmt || node),
      end_line: ml.sf.getLineAndCharacterOfPosition(node.getEnd()).line + 1,
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
      source: (this.f.stmt || node).getText(ml.sf),
      locals: {},
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
    const body = node.body;
    if (ts.isBlock(body)) fn.body = this.block(body.statements, body);
    else {
      try {
        const v = this.coerce(this.expr(body, sig.ret), sig.ret);
        fn.body = [{ s: "Return", loc: ml.loc(body), value: v }];
      } catch (e) {
        if (!(e instanceof LowerError)) throw e;
        this.unsupported.push([e.message, e.line || ml.line(body)]);
        fn.body = [{ s: "Unsupported", loc: ml.loc(body), reason: e.message }];
      }
    }
    fn.locals = { ...this.env };
    fn.intents = this.intents;
    return fn;
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
    if (ts.isBlock(s)) return this.block(s.statements, s);
    return this.stmt(s);
  }

  declare(name, ty, node) {
    const old = this.env[name];
    if (!old) this.env[name] = ty;
    else if (!tyEq(old, ty)) {
      if (old.k === "real" && ty.k === "int") return;
      if (old.k === "list" && ty.k === "list" && ty.elem.k === "none") return;
      throw this.err(`variable '${name}' changes type from ${tyStr(old)} to ${tyStr(ty)}`, node);
    }
  }

  coerce(e, ty) {
    if (ty && ty.k === "real" && e.ty.k === "int") return { e: "Builtin", ty: REAL, loc: e.loc, name: "to_real", args: [e] };
    if (ty && ty.k === "list" && e.e === "ListLit" && e.elems.length === 0) return { ...e, ty };
    return e;
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

  assignTo(name, valueNode, node, op = null) {
    const loc = this.ml.loc(node);
    const known = this.env[name];
    if (!known) throw this.err(`assignment to undeclared variable '${name}'`, node);
    if (this.sig.params.some((p) => p.name === name) && known.k === "list") throw this.err(`rebinding array parameter '${name}' is not supported`, node);
    let v = this.expr(valueNode, known);
    if (op) {
      const cur = { e: "Var", ty: known, loc, name };
      v = this.arith(op, cur, v, node);
    }
    v = this.coerce(v, known);
    if (v.ty.k === "list" && valueNode && ts.isIdentifier(valueNode)) throw this.err(`'${name} = ${valueNode.text}' would alias an array; copy with '${valueNode.text}.slice()'`, node);
    if (!tyEq(v.ty, known) && !(known.k === "list" && v.ty.k === "list" && v.ty.elem.k === "none")) throw this.err(`cannot assign ${tyStr(v.ty)} to '${name}' of type ${tyStr(known)}`, node);
    return [{ s: "Assign", loc, name, value: v }];
  }

  exprStatement(e, node) {
    const K = ts.SyntaxKind;
    const loc = this.ml.loc(node);
    if (ts.isParenthesizedExpression(e)) return this.exprStatement(e.expression, node);
    if (ts.isBinaryExpression(e)) {
      const k = e.operatorToken.kind;
      const ops = { [K.PlusEqualsToken]: "add", [K.MinusEqualsToken]: "sub", [K.AsteriskEqualsToken]: "mul", [K.SlashEqualsToken]: "rdiv", [K.PercentEqualsToken]: "tmod" };
      if (k === K.EqualsToken || ops[k]) {
        if (ts.isIdentifier(e.left)) return this.assignTo(e.left.text, e.right, node, ops[k] || null);
        if (ts.isElementAccessExpression(e.left) && ts.isIdentifier(e.left.expression)) {
          const name = e.left.expression.text;
          const t = this.env[name];
          if (!t || t.k !== "list") throw this.err(`'${name}[...] = ...' needs '${name}' to be an array`, node);
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
    if ((ts.isPostfixUnaryExpression(e) || ts.isPrefixUnaryExpression(e)) && (e.operator === K.PlusPlusToken || e.operator === K.MinusMinusToken)) {
      if (!ts.isIdentifier(e.operand)) throw this.err("++/-- is supported on variables only", node);
      const name = e.operand.text;
      const t = this.env[name];
      if (!isNum(t)) throw this.err(`'${name}' is not a number`, node);
      const one = { e: "Lit", ty: t, loc, value: 1 };
      const cur = { e: "Var", ty: t, loc, name };
      return [{ s: "Assign", loc, name, value: { e: "Binary", ty: t, loc, op: e.operator === K.PlusPlusToken ? "add" : "sub", left: cur, right: one } }];
    }
    if (ts.isCallExpression(e)) {
      const c = e.expression;
      if (ts.isPropertyAccessExpression(c) && ts.isIdentifier(c.expression) && c.expression.text === "console") return [];
      if (ts.isPropertyAccessExpression(c) && c.name.text === "push" && ts.isIdentifier(c.expression)) {
        const name = c.expression.text;
        let t = this.env[name];
        if (!t || t.k !== "list") throw this.err(`'${name}.push' needs '${name}' to be an array`, node);
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
    throw this.err(`unsupported expression statement '${e.getText(this.ml.sf).slice(0, 40)}'`, node);
  }

  _stmt(s) {
    const K = ts.SyntaxKind;
    const loc = this.ml.loc(s);
    if (ts.isEmptyStatement(s)) return [];
    if (ts.isBlock(s)) return this.block(s.statements, s);
    if (ts.isVariableStatement(s)) {
      const out = [];
      for (const d of s.declarationList.declarations) {
        if (!ts.isIdentifier(d.name)) throw this.err("destructuring is not supported", s);
        const name = d.name.text;
        let ty = d.type ? this.ml.typeOf(d.type, this.intSet.has(name)) : null;
        if (ty && ty.k === "real" && this.intSet.has(name)) ty = INT;
        if (!d.initializer) {
          if (!ty) throw this.err(`'${name}' needs a type or an initializer`, s);
          this.declare(name, ty, s);
          continue;
        }
        let v = this.expr(d.initializer, ty);
        if (!ty) {
          ty = v.ty;
          if (ty.k === "int" && !this.intSet.has(name)) ty = REAL;
          if (ty.k === "list" && ty.elem.k === "none") ty = ty; // refined by push
        }
        if (v.ty.k === "list" && ts.isIdentifier(d.initializer)) throw this.err(`'${name} = ${d.initializer.text}' would alias an array; copy with '${d.initializer.text}.slice()'`, s);
        this.declare(name, ty, s);
        v = this.coerce(v, this.env[name]);
        out.push({ s: "Assign", loc, name, value: v });
      }
      return out;
    }
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
    if (ts.isForStatement(s)) return this.forStmt(s, loc);
    if (ts.isForOfStatement(s)) {
      const cls = this.loopContracts(s);
      const d = s.initializer;
      if (!(ts.isVariableDeclarationList(d) && d.declarations.length === 1 && ts.isIdentifier(d.declarations[0].name))) throw this.err("use 'for (const x of xs)'", s);
      const elem = d.declarations[0].name.text;
      const seq = this.expr(s.expression);
      if (seq.ty.k !== "list") throw this.err("for-of needs an array", s);
      let index = null;
      for (const cl of cls) if (cl.keyword === "index") index = cl.payload.trim();
      const idx = index || `i$${++this.tmp}`;
      this.declare(idx, INT, s);
      this.declare(elem, seq.ty.elem, s);
      const body = this.inner(s.statement);
      if (ts.isIdentifier(s.expression) && assigned(body).has(s.expression.text)) throw this.err(`loop body modifies '${s.expression.text}' while iterating over it`, s);
      const { invs, dec } = this.loopClauses(cls);
      if (dec) throw this.err("a for-of loop terminates by construction; remove '@decreases'", s);
      return [{ s: "ForEach", loc, elem, idx, seq, invariants: invs, body, idx_visible: !!index }];
    }
    if (ts.isReturnStatement(s)) {
      if (!s.expression) return [{ s: "Return", loc, value: null }];
      if (this.sig.ret.k === "none") throw this.err("function returns a value but is declared void", s);
      const v = this.coerce(this.expr(s.expression, this.sig.ret), this.sig.ret);
      if (!tyEq(v.ty, this.sig.ret)) throw this.err(`returns ${tyStr(v.ty)} but is declared to return ${tyStr(this.sig.ret)}`, s);
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
    if (ts.isThrowStatement(s)) return [{ s: "Raise", loc, what: s.expression ? s.expression.getText(this.ml.sf).slice(0, 60) : "exception" }];
    throw this.err(`unsupported statement: ${K[s.kind]}`, s);
  }

  forStmt(s, loc) {
    const K = ts.SyntaxKind;
    const cls = this.loopContracts(s);
    // Canonical counted loop: for (let i = lo; i < hi; i++) with i and hi's
    // variables untouched by the body  ==>  ForRange (same semantics).
    const init = s.initializer, cond = s.condition, inc = s.incrementor;
    if (init && ts.isVariableDeclarationList(init) && init.declarations.length === 1 && ts.isIdentifier(init.declarations[0].name) && init.declarations[0].initializer && cond && inc && ts.isBinaryExpression(cond) && cond.operatorToken.kind === K.LessThanToken && ts.isIdentifier(cond.left) && cond.left.text === init.declarations[0].name.text) {
      const v = cond.left.text;
      const isInc =
        ((ts.isPostfixUnaryExpression(inc) || ts.isPrefixUnaryExpression(inc)) && inc.operator === K.PlusPlusToken && ts.isIdentifier(inc.operand) && inc.operand.text === v) ||
        (ts.isBinaryExpression(inc) && inc.operatorToken.kind === K.PlusEqualsToken && ts.isIdentifier(inc.left) && inc.left.text === v && ts.isNumericLiteral(inc.right) && inc.right.text === "1");
      if (isInc) {
        const lo = this.expr(init.declarations[0].initializer);
        const hiNode = cond.right;
        const hi = this.expr(hiNode);
        if (lo.ty.k === "int" && hi.ty.k === "int") {
          this.declare(v, INT, s);
          const body = this.inner(s.statement);
          const mod = assigned(body);
          const hiVars = new Set(varsIn(hi));
          if (!mod.has(v) && ![...hiVars].some((x) => mod.has(x))) {
            const { invs, dec } = this.loopClauses(cls);
            if (dec) throw this.err("this counted loop terminates by construction; remove '@decreases'", s);
            return [{ s: "ForRange", loc, var: v, lo, hi, invariants: invs, body }];
          }
          // fall through to the general form
          const { invs, dec } = this.loopClauses(cls);
          const c = this.cond(cond);
          const step = this.exprStatement(inc, inc);
          return [{ s: "Assign", loc, name: v, value: lo }, { s: "While", loc, cond: c, invariants: invs, decreases: dec, body, step }];
        }
      }
    }
    const out = [];
    if (init) {
      if (ts.isVariableDeclarationList(init)) out.push(...this._stmt(ts.factory.createVariableStatement(undefined, init)).map((x) => ({ ...x, loc })));
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
    if (name in this.env) return this.env[name];
    throw this.err(`unknown name '${name}'`, this.nline(node));
  }

  cond(n) {
    return this.truthy(this.expr(n), n);
  }

  truthy(e, node) {
    if (e.ty.k === "bool") return e;
    if (isNum(e.ty)) return { e: "Binary", ty: BOOL, loc: e.loc, op: "ne", left: e, right: { e: "Lit", ty: e.ty, loc: e.loc, value: 0 } };
    if (e.ty.k === "str") return { e: "Binary", ty: BOOL, loc: e.loc, op: "ne", left: e, right: { e: "Lit", ty: STR, loc: e.loc, value: "" } };
    throw this.err(`a ${tyStr(e.ty)} is always truthy in JavaScript; compare explicitly`, this.nline(node));
  }

  numPair(a, b, node) {
    if (!(isNum(a.ty) && isNum(b.ty))) throw this.err(`arithmetic on ${tyStr(a.ty)} and ${tyStr(b.ty)}`, this.nline(node));
    if (a.ty.k === "real" || b.ty.k === "real") return [this.coerce(a, REAL), this.coerce(b, REAL), REAL];
    return [a, b, INT];
  }

  arith(op, a, b, node) {
    const loc = this.nloc(node);
    if (op === "rdiv") {
      const [x, y] = this.numPair(a, b, node);
      return { e: "Binary", ty: REAL, loc, op: "rdiv", left: this.coerce(x, REAL), right: this.coerce(y, REAL) };
    }
    if (op === "add" && (a.ty.k === "str" || b.ty.k === "str")) throw this.err("string concatenation is not supported", this.nline(node));
    const [x, y, t] = this.numPair(a, b, node);
    return { e: "Binary", ty: t, loc, op, left: x, right: y };
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
    if (ts.isIdentifier(n)) {
      if (this.spec && n.text === "result" && this.resultTy && !(this.bound && "result" in this.bound)) {
        if (this.resultTy.k === "none") throw this.err("'result' used but the function returns nothing", this.nline(n));
        return { e: "Result", ty: this.resultTy, loc };
      }
      return { e: "Var", ty: this.lookup(n.text, n), loc, name: n.text };
    }
    if (ts.isPrefixUnaryExpression(n)) {
      const a = this.expr(n.operand);
      if (n.operator === K.ExclamationToken) return { e: "Unary", ty: BOOL, loc, op: "not", arg: this.truthy(a, n.operand) };
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
        if (isNum(a.ty) && isNum(b.ty)) [a, b] = this.numPair(a, b, n);
        else throw this.err(`conditional branches have types ${tyStr(a.ty)} and ${tyStr(b.ty)}`, this.nline(n));
      }
      return { e: "Ite", ty: a.ty, loc, cond: c, then: a, orelse: b };
    }
    if (ts.isCallExpression(n)) return this.call(n, loc, expect);
    if (ts.isElementAccessExpression(n)) {
      const seq = this.expr(n.expression);
      if (seq.ty.k !== "list") throw this.err(`cannot index a ${tyStr(seq.ty)}`, this.nline(n));
      return { e: "Index", ty: seq.ty.elem, loc, seq, idx: this.index(n.argumentExpression), wrap: false };
    }
    if (ts.isPropertyAccessExpression(n)) {
      if (n.questionDotToken) throw this.err("optional chaining is not supported", this.nline(n));
      const name = n.name.text;
      const obj = this.expr(n.expression);
      if (obj.ty.k === "list" && name === "length") return { e: "Builtin", ty: INT, loc, name: "len", args: [obj] };
      if (obj.ty.k === "record") {
        const f = obj.ty.fields.find((x) => x[0] === name);
        if (!f) throw this.err(`${obj.ty.name} has no field '${name}'`, this.nline(n));
        return { e: "Field", ty: f[1], loc, obj, name };
      }
      throw this.err(`unsupported property '.${name}' on ${tyStr(obj.ty)}`, this.nline(n));
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
          vals[p.name.text] = this.coerce({ e: "Var", ty: this.lookup(p.name.text, p), loc, name: p.name.text }, ft[1]);
        } else throw this.err("unsupported object literal member", this.nline(p));
      }
      const missing = expect.fields.filter((f) => !(f[0] in vals)).map((f) => f[0]);
      if (missing.length) throw this.err(`${expect.name} literal is missing ${missing.join(", ")}`, this.nline(n));
      return { e: "RecordLit", ty: expect, loc, fields: expect.fields.map((f) => [f[0], vals[f[0]]]) };
    }
    if (ts.isAsExpression(n) || ts.isNonNullExpression(n) || ts.isSatisfiesExpression?.(n)) throw this.err("type assertions ('as', '!') are not supported: they hide exactly what telic checks", this.nline(n));
    throw this.err(`unsupported expression: ${K[n.kind]}`, this.nline(n));
  }

  binary(n, loc) {
    const K = ts.SyntaxKind;
    const k = n.operatorToken.kind;
    if (k === K.AmpersandAmpersandToken || k === K.BarBarToken) {
      const a = this.cond(n.left), b = this.cond(n.right);
      return { e: "Binary", ty: BOOL, loc, op: k === K.AmpersandAmpersandToken ? "and" : "or", left: a, right: b };
    }
    const cmp = { [K.LessThanToken]: "lt", [K.LessThanEqualsToken]: "le", [K.GreaterThanToken]: "gt", [K.GreaterThanEqualsToken]: "ge", [K.EqualsEqualsEqualsToken]: "eq", [K.ExclamationEqualsEqualsToken]: "ne", [K.EqualsEqualsToken]: "eq", [K.ExclamationEqualsToken]: "ne" };
    if (cmp[k]) {
      let a = this.expr(n.left), b = this.expr(n.right);
      if (isNum(a.ty) && isNum(b.ty)) [a, b] = this.numPair(a, b, n);
      else if (!tyEq(a.ty, b.ty)) throw this.err(`comparing ${tyStr(a.ty)} with ${tyStr(b.ty)}`, this.nline(n));
      else if (!["eq", "ne"].includes(cmp[k]) && !isNum(a.ty)) throw this.err(`ordering comparison on ${tyStr(a.ty)} is not supported`, this.nline(n));
      else if (a.ty.k === "list" || a.ty.k === "record") throw this.err("=== on arrays/objects compares identity, not contents; compare fields explicitly", this.nline(n));
      return { e: "Binary", ty: BOOL, loc, op: cmp[k], left: a, right: b };
    }
    const ar = { [K.PlusToken]: "add", [K.MinusToken]: "sub", [K.AsteriskToken]: "mul", [K.SlashToken]: "rdiv", [K.PercentToken]: "tmod" };
    if (ar[k]) return this.arith(ar[k], this.expr(n.left), this.expr(n.right), n);
    if (k === K.AsteriskAsteriskToken && ts.isNumericLiteral(n.right) && /^[0-4]$/.test(n.right.text)) {
      const a = this.expr(n.left);
      const p = Number(n.right.text);
      if (p === 0) return { e: "Lit", ty: a.ty, loc, value: 1 };
      let out = a;
      for (let i = 1; i < p; i++) out = { e: "Binary", ty: a.ty, loc, op: "mul", left: out, right: a };
      return out;
    }
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
        if (m === "abs") {
          const x = this.expr(args[0]);
          if (!isNum(x.ty)) throw this.err("Math.abs needs a number", this.nline(n));
          return { e: "Builtin", ty: x.ty, loc, name: "abs", args: [x] };
        }
        if (m === "min" || m === "max") {
          let xs = args.map((a) => this.expr(a));
          if (xs.length < 2 || !xs.every((x) => isNum(x.ty))) throw this.err(`Math.${m} needs two or more numbers`, this.nline(n));
          const t = xs.some((x) => x.ty.k === "real") ? REAL : INT;
          return { e: "Builtin", ty: t, loc, name: m, args: xs.map((x) => this.coerce(x, t)) };
        }
        throw this.err(`Math.${m} is not supported`, this.nline(n));
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
      // range(lo, hi).every(i => ...)   (spec helper)
      if ((m === "every" || m === "some") && ts.isCallExpression(c.expression) && ts.isIdentifier(c.expression.expression) && c.expression.expression.text === "range") {
        const ra = c.expression.arguments.map((a) => this.expr(a));
        if (ra.length !== 2 || !ra.every((x) => x.ty.k === "int")) throw this.err("range(lo, hi) needs two integers", this.nline(n));
        const lam = this.lambda(args[0], [{ ty: INT }]);
        const idx = lam.names[0] || `_${++this.tmp}`;
        return { e: "Quant", ty: BOOL, loc, kind: m === "every" ? "forall" : "exists", idx, lo: ra[0], hi: ra[1], body: this.truthy(lam.body, args[0]), elem: null, seq: null };
      }
      const obj = this.expr(c.expression);
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
        throw this.err(`array method .${m}() is not supported`, this.nline(n));
      }
      throw this.err(`unsupported method call .${m}()`, this.nline(n));
    }
    if (!ts.isIdentifier(c)) throw this.err("unsupported call", this.nline(n));
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
    const sig = this.ml.sigs[name];
    if (!sig) throw this.err(`call to '${name}', which telic cannot see (define it in a checked file with a contract)`, this.nline(n));
    if (args.length !== sig.params.length) throw this.err(`'${name}' takes ${sig.params.length} arguments, got ${args.length}`, this.nline(n));
    const lowered = sig.params.map((p, i) => {
      const v = this.coerce(this.expr(args[i], p.ty), p.ty);
      if (!tyEq(v.ty, p.ty) && !(p.ty.k === "list" && v.ty.k === "list" && v.ty.elem.k === "none")) {
        if (p.ty.k === "int" && v.ty.k === "real") throw this.err(`argument '${p.name}' of '${name}' must be an integer; telic cannot show this number is one`, this.nline(n));
        throw this.err(`argument '${p.name}' of '${name}' expects ${tyStr(p.ty)}, got ${tyStr(v.ty)}`, this.nline(n));
      }
      return v;
    });
    return { e: "Call", ty: sig.ret, loc, func: name, args: lowered };
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

function main() {
  const [root, ...files] = process.argv.slice(2);
  const out = [];
  for (const file of files) {
    const text = fs.readFileSync(file, "utf8");
    const sf = ts.createSourceFile(file, text, ts.ScriptTarget.Latest, true, file.endsWith("x") ? ts.ScriptKind.TSX : ts.ScriptKind.TS);
    const rel = path.relative(root, file);
    const ml = new ModuleLowerer(file, rel, sf);
    let mod;
    try {
      mod = ml.run();
    } catch (e) {
      mod = { path: rel, language: "typescript", source: text, functions: [], intents: [], records: {}, problems: [[`internal error: ${e.message}`, e.line || 0]], assumptions: JS_ASSUMPTIONS };
    }
    if (sf.parseDiagnostics && sf.parseDiagnostics.length) {
      const d = sf.parseDiagnostics[0];
      const lc = sf.getLineAndCharacterOfPosition(d.start || 0);
      mod.problems.push([`syntax error: ${ts.flattenDiagnosticMessageText(d.messageText, " ")}`, lc.line + 1]);
    }
    mod.file = file;
    out.push(mod);
  }
  process.stdout.write(JSON.stringify(out));
}

main();
