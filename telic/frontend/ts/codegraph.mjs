// Calls through function values in TypeScript: which code of the module a
// call may run when no Call in the IR names it (see ir.CodeGraph).

import { createRequire } from "node:module";

const require = createRequire(import.meta.url);
const ts = require("typescript");

const isFn = (n) => ts.isFunctionDeclaration(n) || ts.isFunctionExpression(n) || ts.isArrowFunction(n) || ts.isMethodDeclaration(n) || ts.isConstructorDeclaration(n) || ts.isGetAccessorDeclaration(n) || ts.isSetAccessorDeclaration(n);
const READS = new Set(["typeof", "String", "Boolean", "isNaN"]);

const strip = (e) => {
  while (e && (ts.isParenthesizedExpression(e) || ts.isAsExpression(e) || ts.isNonNullExpression(e) || ts.isTypeAssertionExpression(e) || (ts.isSatisfiesExpression && ts.isSatisfiesExpression(e)))) e = e.expression;
  return e;
};

// `checked`: functions lowered into the IR (names), whose direct calls are
// Calls already; `imports`: names imported from checked modules -> [path,
// name]; `namespaces`: `import * as ns` of checked modules -> path.
export function codeGraph(sf, checked, imports, namespaces) {
  const g = { units: {}, calls: [], bindings: {}, imports: { ...imports }, escaped: [] };
  const escaped = new Set();
  const at = (n) => {
    const p = sf.getLineAndCharacterOfPosition(n.getStart(sf));
    return [p.line + 1, p.character];
  };
  const top = new Map(); // module-level function name -> node (declarations and `const f = () => ...`)
  const classes = new Map();
  const methods = new Map(); // method name -> Set of 'Class.name'
  const unitIds = new Map();
  const moduleScope = { parent: null, params: new Set(), opaque: new Set(), defs: new Map(), assigns: new Map(), cls: null };
  const addAssign = (scope, name, v) => {
    if (!scope.assigns.has(name)) scope.assigns.set(name, []);
    scope.assigns.get(name).push(v);
  };
  const bindNames = (b, into) => {
    if (ts.isIdentifier(b)) into.add(b.text);
    else if (b && b.elements) for (const el of b.elements) if (!ts.isOmittedExpression(el)) bindNames(el.name, into);
  };
  const memberName = (m) => (m.name && (ts.isIdentifier(m.name) || ts.isPrivateIdentifier(m.name)) ? m.name.text : null);
  const classMembers = (cname, node) => {
    for (const m of node.members) {
      const n = memberName(m);
      if (!n) continue;
      if (ts.isMethodDeclaration(m)) {
        if (!methods.has(n)) methods.set(n, new Set());
        methods.get(n).add(`${cname}.${n}`);
      }
    }
  };
  for (const st of sf.statements) {
    if (ts.isFunctionDeclaration(st) && st.name) top.set(st.name.text, st);
    else if (ts.isClassDeclaration(st) && st.name) {
      classes.set(st.name.text, st);
      classMembers(st.name.text, st);
    } else if (ts.isVariableStatement(st)) {
      for (const d of st.declarationList.declarations) {
        const init = d.initializer && strip(d.initializer);
        if (ts.isIdentifier(d.name) && init && (ts.isArrowFunction(init) || ts.isFunctionExpression(init)) && checked.has(d.name.text)) top.set(d.name.text, init);
        else if (ts.isIdentifier(d.name) && d.initializer) addAssign(moduleScope, d.name.text, d.initializer);
        else if (ts.isIdentifier(d.name)) moduleScope.opaque.add(d.name.text);
        else bindNames(d.name, moduleScope.opaque);
      }
    }
  }
  // module-level names assigned from inside functions: anything
  const visitAll = (n, f) => {
    f(n);
    ts.forEachChild(n, (c) => visitAll(c, f));
  };
  const thisFields = new Set();
  const callableAttrs = new Set();
  const isFnType = (t) => !!t && (ts.isFunctionTypeNode(t) || (ts.isTypeReferenceNode(t) && /^(Function|Callback|Handler)/.test(t.typeName.getText(sf))) || (ts.isUnionTypeNode(t) && t.types.some(isFnType)) || (ts.isParenthesizedTypeNode(t) && isFnType(t.type)));
  const fnParams = new Set();
  visitAll(sf, (n) => {
    if (ts.isBinaryExpression(n) && n.operatorToken.kind === ts.SyntaxKind.EqualsToken && ts.isIdentifier(n.left) && moduleScope.assigns.has(n.left.text)) {
      let p = n.parent;
      while (p && !isFn(p)) p = p.parent;
      if (p) moduleScope.opaque.add(n.left.text);
      else addAssign(moduleScope, n.left.text, n.right);
    }
    if (ts.isParameter(n) && ts.isIdentifier(n.name) && isFnType(n.type)) fnParams.add(n.name.text);
    if (ts.isPropertyDeclaration(n) && memberName(n)) {
      thisFields.add(memberName(n));
      if (isFnType(n.type) || (n.initializer && (ts.isArrowFunction(strip(n.initializer)) || ts.isFunctionExpression(strip(n.initializer))))) callableAttrs.add(memberName(n));
    }
    if (ts.isPropertySignature(n) && memberName(n) && isFnType(n.type)) callableAttrs.add(memberName(n));
    if (ts.isObjectLiteralExpression(n)) {
      for (const p of n.properties) {
        const name = p.name && ts.isIdentifier(p.name) ? p.name.text : null;
        if (!name) continue;
        if (ts.isMethodDeclaration(p) || (ts.isPropertyAssignment(p) && (ts.isArrowFunction(strip(p.initializer)) || ts.isFunctionExpression(strip(p.initializer)) || ts.isIdentifier(strip(p.initializer))))) callableAttrs.add(name);
      }
    }
  });
  visitAll(sf, (n) => {
    if (ts.isBinaryExpression(n) && n.operatorToken.kind === ts.SyntaxKind.EqualsToken && ts.isPropertyAccessExpression(n.left)) {
      if (n.left.expression.kind === ts.SyntaxKind.ThisKeyword) thisFields.add(n.left.name.text);
      const r = strip(n.right);
      if (ts.isArrowFunction(r) || ts.isFunctionExpression(r) || (ts.isIdentifier(r) && (top.has(r.text) || fnParams.has(r.text)))) callableAttrs.add(n.left.name.text);
    }
  });

  const unitOf = (n) => {
    if (!unitIds.has(n)) {
      const [line, col] = at(n);
      const name = n.name && ts.isIdentifier(n.name) ? n.name.text : ts.isArrowFunction(n) ? "arrow" : "function";
      const id = `<${name}:${line}:${col}>`;
      unitIds.set(n, id);
      const label = n.name && ts.isIdentifier(n.name) ? `'${name}' at line ${line}` : `the ${ts.isArrowFunction(n) ? "arrow function" : "function"} at line ${line}`;
      g.units[id] = [line, col, label, n.getText(sf)];
    }
    return unitIds.get(n);
  };

  const scopeOf = (fn, parent, cls) => {
    const s = { parent, params: new Set(), opaque: new Set(), defs: new Map(), assigns: new Map(), cls };
    for (const p of fn.parameters || []) bindNames(p.name, s.params);
    const walk = (n) => {
      if (n !== fn && (isFn(n) || ts.isClassDeclaration(n) || ts.isClassExpression(n))) {
        if (ts.isFunctionDeclaration(n) && n.name) s.defs.set(n.name.text, unitOf(n));
        if (ts.isClassDeclaration(n) && n.name) s.opaque.add(n.name.text);
        return;
      }
      if (ts.isVariableDeclaration(n)) {
        if (ts.isIdentifier(n.name) && n.initializer) addAssign(s, n.name.text, n.initializer);
        else bindNames(n.name, s.opaque);
      } else if (ts.isBinaryExpression(n) && n.operatorToken.kind === ts.SyntaxKind.EqualsToken && ts.isIdentifier(n.left)) {
        addAssign(s, n.left.text, n.right);
      } else if (ts.isCatchClause(n) && n.variableDeclaration) bindNames(n.variableDeclaration.name, s.opaque);
      ts.forEachChild(n, walk);
    };
    if (fn.body) walk(fn.body);
    for (const k of s.params) s.assigns.delete(k);
    for (const k of s.opaque) s.assigns.delete(k);
    for (const [k, vs] of s.assigns) if (vs.some((v) => ts.isVariableDeclaration(v.parent) && ts.isVariableDeclarationList(v.parent.parent) && v.parent.parent.parent && (ts.isForOfStatement(v.parent.parent.parent) || ts.isForInStatement(v.parent.parent.parent)))) s.opaque.add(k);
    return s;
  };

  const lookup = (x, scope, seen) => {
    for (let s = scope; s; s = s.parent) {
      if (s.params.has(x) || s.opaque.has(x)) return new Set(["?"]);
      if (s.defs.has(x)) return new Set([s.defs.get(x)]);
      if (s.assigns.has(x)) {
        if (seen.has(s) && seen.get(s).has(x)) return new Set();
        if (!seen.has(s)) seen.set(s, new Set());
        seen.get(s).add(x);
        const out = new Set();
        for (const v of s.assigns.get(x)) for (const t of resolve(v, s, seen)) out.add(t);
        return out;
      }
      if (!s.parent) {
        if (top.has(x)) return new Set([x]);
        if (classes.has(x)) return new Set([`${x}.__init__`]);
        if (x in imports) return new Set([x]);
        return new Set();
      }
    }
    return new Set();
  };

  const resolve = (e0, scope, seen = new Map()) => {
    const e = strip(e0);
    if (!e) return new Set();
    if (ts.isIdentifier(e)) return lookup(e.text, scope, seen);
    if (ts.isArrowFunction(e) || ts.isFunctionExpression(e)) return new Set([unitOf(e)]);
    if (ts.isPropertyAccessExpression(e)) {
      const b = e.name.text, v = strip(e.expression);
      if (v.kind === ts.SyntaxKind.ThisKeyword && scope.cls) {
        const own = [...(methods.get(b) || [])].filter((m) => m.startsWith(scope.cls + "."));
        if (own.length) return new Set(own);
        const inherits = !classes.has(scope.cls) || !!classes.get(scope.cls).heritageClauses;
        return new Set([...(inherits ? methods.get(b) || [] : []), ...(thisFields.has(b) || callableAttrs.has(b) ? ["?"] : [])]);
      }
      if (ts.isIdentifier(v) && classes.has(v.text) && lookup(v.text, scope, new Map()).has(`${v.text}.__init__`)) return new Set((methods.get(b) || new Set()).has(`${v.text}.${b}`) ? [`${v.text}.${b}`] : []);
      if (ts.isIdentifier(v) && v.text in namespaces) return new Set([`${v.text}.${b}`]);
      return new Set([...(methods.get(b) || []), ...(callableAttrs.has(b) ? ["?"] : [])]);
    }
    if (ts.isConditionalExpression(e)) return new Set([...resolve(e.whenTrue, scope, seen), ...resolve(e.whenFalse, scope, seen)]);
    if (ts.isBinaryExpression(e) && [ts.SyntaxKind.BarBarToken, ts.SyntaxKind.AmpersandAmpersandToken, ts.SyntaxKind.QuestionQuestionToken].includes(e.operatorToken.kind)) return new Set([...resolve(e.left, scope, seen), ...resolve(e.right, scope, seen)]);
    if (ts.isBinaryExpression(e) && e.operatorToken.kind === ts.SyntaxKind.EqualsToken) return resolve(e.right, scope, seen);
    if (ts.isCallExpression(e) && ts.isPropertyAccessExpression(strip(e.expression)) && strip(e.expression).name.text === "bind") return resolve(strip(e.expression).expression, scope, seen);
    if (ts.isCallExpression(e) || ts.isElementAccessExpression(e) || ts.isAwaitExpression(e)) return new Set(["?"]);
    return new Set();
  };

  const value = (e, ctx) => {
    const s = strip(e);
    if (s.kind === ts.SyntaxKind.ThisKeyword) return new Set();
    const got = [...resolve(s, ctx.scope)].filter((t) => t !== "?");
    if (ts.isIdentifier(s) && got.length === 1 && got[0] === `${s.text}.__init__`) return new Set();
    // a name from another module may be data there, not code
    return new Set(got.map((t) => (t in imports || t.split(".")[0] in namespaces ? `=${t}` : t)));
  };

  const site = (ctx, node, label, targets) => {
    if (!targets.size || ctx.unit === null) return;
    const [line, col] = at(node);
    g.calls.push([ctx.unit, line, col, label.length <= 40 ? label : label.slice(0, 37) + "...", [...targets].sort()]);
  };

  const isValueRef = (n) => ts.isIdentifier(n) || ts.isPropertyAccessExpression(n) || ts.isArrowFunction(n) || ts.isFunctionExpression(n) || (ts.isCallExpression(n) && ts.isPropertyAccessExpression(strip(n.expression)) && strip(n.expression).name.text === "bind");

  // Is `n` used as a value: not called, not a receiver, not a name being declared or assigned?
  const valuePosition = (n) => {
    const p = n.parent;
    if (!p) return false;
    if ((ts.isCallExpression(p) || ts.isNewExpression(p)) && p.expression === n) return false;
    if (ts.isPropertyAccessExpression(p) && p.expression === n) return false;
    if (ts.isPropertyAccessExpression(p) && p.name === n) return false;
    if ((ts.isVariableDeclaration(p) || ts.isParameter(p) || ts.isFunctionDeclaration(p) || ts.isClassDeclaration(p) || ts.isPropertyDeclaration(p) || ts.isMethodDeclaration(p) || ts.isPropertyAssignment(p) || ts.isBindingElement(p)) && p.name === n) return false;
    if (ts.isImportSpecifier(p) || ts.isImportClause(p) || ts.isNamespaceImport(p) || ts.isExportSpecifier(p)) return false;
    if (ts.isBinaryExpression(p) && p.left === n && p.operatorToken.kind >= ts.SyntaxKind.FirstAssignment && p.operatorToken.kind <= ts.SyntaxKind.LastAssignment) return false;
    if (ts.isTypeReferenceNode(p) || ts.isTypeQueryNode(p) || ts.isQualifiedName(p) || ts.isExpressionWithTypeArguments(p) || ts.isHeritageClause(p)) return false;
    if (ts.isPrefixUnaryExpression(p) || ts.isPostfixUnaryExpression(p) || ts.isTypeOfExpression(p)) return false;
    if (ts.isBinaryExpression(p) && [ts.SyntaxKind.EqualsEqualsEqualsToken, ts.SyntaxKind.ExclamationEqualsEqualsToken, ts.SyntaxKind.EqualsEqualsToken, ts.SyntaxKind.ExclamationEqualsToken, ts.SyntaxKind.InstanceOfKeyword, ts.SyntaxKind.InKeyword].includes(p.operatorToken.kind)) return false;
    // a tracked binding (`const g = f`, `g = f`): its uses are followed by name
    if (ts.isVariableDeclaration(p) && p.initializer === n && ts.isIdentifier(p.name)) return false;
    if (ts.isBinaryExpression(p) && p.right === n && p.operatorToken.kind === ts.SyntaxKind.EqualsToken && ts.isIdentifier(p.left)) return false;
    if ((ts.isParenthesizedExpression(p) || ts.isAsExpression(p) || ts.isNonNullExpression(p) || ts.isConditionalExpression(p) || (ts.isBinaryExpression(p) && [ts.SyntaxKind.BarBarToken, ts.SyntaxKind.AmpersandAmpersandToken, ts.SyntaxKind.QuestionQuestionToken].includes(p.operatorToken.kind))) && !(ts.isConditionalExpression(p) && p.condition === n)) return valuePosition(p);
    return true;
  };

  const callOf = (node, ctx) => {
    const f = strip(node.expression), scope = ctx.scope;
    const label = node.expression.getText(sf);
    if (ts.isNewExpression(node)) {
      if (!ctx.checked && ts.isIdentifier(f)) site(ctx, node, label, lookup(f.text, scope, new Map()));
    } else if (ts.isIdentifier(f)) {
      const t = resolve(f, scope);
      const direct = ctx.checked && checked.has(f.text) && t.size === 1 && t.has(f.text);
      if (!direct) site(ctx, node, label, t);
    } else if (ts.isPropertyAccessExpression(f)) {
      const v = strip(f.expression), b = f.name.text;
      if (b === "call" || b === "apply") site(ctx, node, label, resolve(v, scope));
      else if (b === "bind") {
        /* a value, not a call */
      } else if (v.kind === ts.SyntaxKind.ThisKeyword && scope.cls) {
        if (!(ctx.checked && methods.has(b))) site(ctx, node, label, resolve(f, scope)); // the IR calls a checked method directly
      } else if (ts.isIdentifier(v) && v.text in namespaces) {
        if (!ctx.checked) site(ctx, node, label, new Set([`${v.text}.${b}`]));
      } else if (callableAttrs.has(b) && !methods.has(b)) site(ctx, node, label, new Set(["?"]));
      else if (!ctx.checked && methods.has(b)) site(ctx, node, label, new Set(methods.get(b)));
    } else {
      const t = resolve(f, scope);
      site(ctx, node, label, t.size ? t : new Set(["?"]));
    }
    const given = new Set();
    const callee = ts.isIdentifier(f) ? f.text : "";
    for (const a of node.arguments || []) {
      const look = (x) => {
        if (isValueRef(x) && valuePosition(x)) for (const t of value(x, ctx)) given.add(t);
        if (!(ts.isArrowFunction(x) || ts.isFunctionExpression(x))) ts.forEachChild(x, look);
      };
      look(a);
    }
    if (given.size && !READS.has(callee)) site(ctx, node, `${label} (given ${[...given].map((t) => (t.startsWith("<") ? t.slice(1).split(":")[0] : t)).sort().join(", ")})`, given);
  };

  const visit = (n, ctx) => {
    if (isFn(n) && !(ts.isFunctionDeclaration(n) && !n.body)) {
      const uid = unitOf(n);
      if ((ts.isArrowFunction(n) || ts.isFunctionExpression(n)) && valuePosition(n)) escaped.add(uid);
      const inner = { unit: uid, checked: false, scope: scopeOf(n, ctx.scope, ctx.scope.cls && (ts.isArrowFunction(n) ? ctx.scope.cls : null)) };
      for (const p of n.parameters || []) if (p.initializer) visit(p.initializer, ctx);
      if (n.body) visit(n.body, inner);
      return;
    }
    if (ts.isClassDeclaration(n) || ts.isClassExpression(n)) {
      const cname = n.name ? n.name.text : "class";
      for (const m of n.members) {
        if (isFn(m) && m.body) {
          const uid = unitOf(m);
          escaped.add(uid); // a method of a class telic does not check
          const inner = { unit: uid, checked: false, scope: scopeOf(m, ctx.scope, cname) };
          visit(m.body, inner);
        } else ts.forEachChild(m, (c) => visit(c, ctx));
      }
      return;
    }
    if (ts.isCallExpression(n) || ts.isNewExpression(n)) {
      callOf(n, ctx);
      ts.forEachChild(n, (c) => visit(c, ctx));
      return;
    }
    if (isValueRef(n) && valuePosition(n)) for (const t of value(n, ctx)) escaped.add(t);
    ts.forEachChild(n, (c) => visit(c, ctx));
  };

  const moduleCtx = { unit: null, checked: false, scope: moduleScope };
  for (const st of sf.statements) {
    if (ts.isFunctionDeclaration(st) && st.name && st.body) {
      const name = st.name.text;
      if (!checked.has(name)) g.units[name] = [...at(st), `'${name}'`, st.getText(sf)];
      visit(st.body, { unit: name, checked: checked.has(name), scope: scopeOf(st, moduleScope, null) });
    } else if (ts.isVariableStatement(st) && st.declarationList.declarations.some((d) => ts.isIdentifier(d.name) && top.get(d.name.text) === (d.initializer && strip(d.initializer)))) {
      for (const d of st.declarationList.declarations) {
        const fn = top.get(d.name.text);
        if (fn && fn === strip(d.initializer)) {
          for (const p of fn.parameters) if (p.initializer) visit(p.initializer, moduleCtx);
          if (ts.isBlock(fn.body)) visit(fn.body, { unit: d.name.text, checked: true, scope: scopeOf(fn, moduleScope, null) });
          else visit(fn.body, { unit: d.name.text, checked: true, scope: scopeOf(fn, moduleScope, null) });
        } else if (d.initializer) visit(d.initializer, moduleCtx);
      }
    } else if (ts.isClassDeclaration(st) && st.name) {
      const cname = st.name.text;
      for (const c of st.heritageClauses || []) visit(c, moduleCtx);
      for (const m of st.members) {
        if (isFn(m) && m.body) {
          const n = memberName(m);
          const key = ts.isConstructorDeclaration(m) ? `${cname}.__init__` : ts.isSetAccessorDeclaration(m) ? `${cname}.${n}.setter` : `${cname}.${n}`;
          if (!checked.has(key)) g.units[key] = [...at(m), `'${key}'`, m.getText(sf)];
          for (const p of m.parameters) if (p.initializer) visit(p.initializer, moduleCtx);
          visit(m.body, { unit: key, checked: checked.has(key), scope: scopeOf(m, moduleScope, cname) });
        } else ts.forEachChild(m, (c) => visit(c, { unit: `${cname}.__init__`, checked: checked.has(`${cname}.__init__`), scope: scopeOf({ parameters: [], body: null }, moduleScope, cname) }));
      }
    } else visit(st, moduleCtx);
  }
  for (const [x] of moduleScope.assigns) {
    const got = lookup(x, moduleScope, new Map());
    if (got.size) g.bindings[x] = [...got].sort();
  }
  g.escaped = [...escaped].sort();
  return g;
}
