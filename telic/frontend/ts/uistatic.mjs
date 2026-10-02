import { createRequire } from "node:module";
import fs from "node:fs";

const require = createRequire(import.meta.url);
const ts = require("typescript");
const input = JSON.parse(fs.readFileSync(0, "utf8"));
const files = new Map(input.files.map((f) => [f.path, f]));
const resolutions = input.resolutions || {};
const fail = (sf, node, why) => { throw new Error(`${sf.fileName}:${sf.getLineAndCharacterOfPosition(node.getStart(sf)).line + 1}: ${why}`); };
const strip = (e) => {
  while (e && (ts.isParenthesizedExpression(e) || ts.isAsExpression(e) || ts.isNonNullExpression(e) || ts.isTypeAssertionExpression(e))) e = e.expression;
  return e;
};
const modeledAria = new Set(["aria-label", "aria-labelledby", "aria-modal", "aria-hidden", "aria-disabled", "aria-checked", "aria-expanded", "aria-pressed", "aria-selected"]);
const modeledTags = new Set(["div", "span", "button", "main", "nav", "aside", "article", "p", "h1", "h2", "h3", "h4", "h5", "h6", "table", "thead", "tbody", "tfoot", "tr", "td", "th", "kbd"]);
const invalidStatic = Symbol("invalid static value");
const lineOf = (sf, n) => sf.getLineAndCharacterOfPosition(n.getStart(sf)).line + 1;

function literal(e, sf) {
  e = strip(e);
  if (!e) return null;
  if (e.kind === ts.SyntaxKind.TrueKeyword) return ["lit", true];
  if (e.kind === ts.SyntaxKind.FalseKeyword) return ["lit", false];
  if (ts.isStringLiteralLike(e)) return ["lit", e.text];
  if (ts.isNumericLiteral(e)) {
    const value = Number(e.text);
    if (!Number.isSafeInteger(value)) fail(sf, e, "numeric UI state and literals must be safe integers");
    return ["lit", value];
  }
  if (e.kind === ts.SyntaxKind.NullKeyword) return ["lit", null];
  return null;
}

function staticValue(e, sf) {
  e = strip(e);
  const lit = literal(e, sf);
  if (lit) return lit[1];
  if (ts.isArrayLiteralExpression(e)) {
    const values = [];
    for (const item of e.elements) {
      if (!ts.isExpression(item) || ts.isSpreadElement(item)) return invalidStatic;
      const value = staticValue(item, sf);
      if (value === invalidStatic) return invalidStatic;
      values.push(value);
    }
    return values;
  }
  if (ts.isObjectLiteralExpression(e)) {
    const values = {};
    for (const property of e.properties) {
      if (!ts.isPropertyAssignment(property) || ts.isComputedPropertyName(property.name)) return invalidStatic;
      const key = ts.isIdentifier(property.name) || ts.isStringLiteralLike(property.name) || ts.isNumericLiteral(property.name) ? property.name.text : null;
      const value = staticValue(property.initializer, sf);
      if (key === null || key === "__proto__" || value === invalidStatic) return invalidStatic;
      values[key] = value;
    }
    return values;
  }
  return invalidStatic;
}

function expr(e, sf, states, locals = new Set(), substitutions = new Map(), statePrefix = "") {
  e = strip(e);
  const lit = literal(e, sf);
  if (lit) return lit;
  if (ts.isIdentifier(e)) {
    if (locals.has(e.text)) return ["local", e.text];
    if (states.has(e.text)) return ["state", `${statePrefix}${e.text}`];
    if (substitutions.has(e.text)) return substitutions.get(e.text);
    fail(sf, e, `reads unmodeled value '${e.text}'`);
  }
  if (ts.isPropertyAccessExpression(e)) return ["member", expr(e.expression, sf, states, locals, substitutions, statePrefix), ["lit", e.name.text]];
  if (ts.isElementAccessExpression(e) && e.argumentExpression) return ["member", expr(e.expression, sf, states, locals, substitutions, statePrefix), expr(e.argumentExpression, sf, states, locals, substitutions, statePrefix)];
  if (ts.isPrefixUnaryExpression(e) && [ts.SyntaxKind.ExclamationToken, ts.SyntaxKind.MinusToken, ts.SyntaxKind.PlusToken].includes(e.operator)) {
    const op = e.operator === ts.SyntaxKind.ExclamationToken ? "not" : e.operator === ts.SyntaxKind.MinusToken ? "neg" : "pos";
    return ["un", op, expr(e.operand, sf, states, locals, substitutions, statePrefix)];
  }
  if (ts.isBinaryExpression(e)) {
    const ops = new Map([
      [ts.SyntaxKind.EqualsEqualsEqualsToken, "eq"],
      [ts.SyntaxKind.ExclamationEqualsEqualsToken, "ne"],
      [ts.SyntaxKind.AmpersandAmpersandToken, "and"], [ts.SyntaxKind.BarBarToken, "or"],
      [ts.SyntaxKind.PlusToken, "add"], [ts.SyntaxKind.MinusToken, "sub"], [ts.SyntaxKind.AsteriskToken, "mul"],
      [ts.SyntaxKind.PercentToken, "mod"], [ts.SyntaxKind.LessThanToken, "lt"], [ts.SyntaxKind.LessThanEqualsToken, "le"],
      [ts.SyntaxKind.GreaterThanToken, "gt"], [ts.SyntaxKind.GreaterThanEqualsToken, "ge"],
    ]);
    const op = ops.get(e.operatorToken.kind);
    if (!op) fail(sf, e, "uses an operator outside the finite UI expression model");
    return ["bin", op, expr(e.left, sf, states, locals, substitutions, statePrefix), expr(e.right, sf, states, locals, substitutions, statePrefix)];
  }
  if (ts.isConditionalExpression(e)) return ["if", expr(e.condition, sf, states, locals, substitutions, statePrefix), expr(e.whenTrue, sf, states, locals, substitutions, statePrefix), expr(e.whenFalse, sf, states, locals, substitutions, statePrefix)];
  fail(sf, e, "uses an expression outside the finite UI model");
}

function jsxText(s) {
  const parts = s.split(/\r?\n/).map((line, i, all) => {
    let x = line.replace(/\t/g, " ");
    if (i !== 0) x = x.replace(/^ +/, "");
    if (i !== all.length - 1) x = x.replace(/ +$/, "");
    return x;
  }).filter(Boolean);
  return parts.join(" ");
}

function scanComponent(path, text, sf, component, asChild = false, componentProps = { values: new Map(), handlers: new Map(), children: null }, statePrefix = "", dynamicMount = false) {
  if (!asChild && component.parameters.length) fail(sf, component.parameters[0], "component props and parameter defaults are outside the source UI model");
  if (asChild) {
    const parameter = component.parameters[0];
    if (component.parameters.length > 1 || parameter && (!ts.isObjectBindingPattern(parameter.name)
        || parameter.initializer || parameter.dotDotDotToken
        || parameter.name.elements.some((e) => !ts.isBindingElement(e) || e.dotDotDotToken || e.initializer || !ts.isIdentifier(e.name)))) {
      fail(sf, parameter || component, "composed component parameters must be a simple destructured props object");
    }
    if (parameter) for (const e of parameter.name.elements) {
        const sourceName = e.propertyName ? e.propertyName.getText(sf) : e.name.text;
        if (!componentProps.values.has(sourceName) && !componentProps.handlers.has(sourceName) && !(sourceName === "children" && componentProps.children)) fail(sf, e, `composed component prop '${sourceName}' has no static binding`);
      }
  }
  const owns = (node, target) => {
    if (node === target) return true;
    let found = false;
    const walk = (x) => { if (found) return; if (x === target) found = true; else ts.forEachChild(x, walk); };
    walk(node);
    return found;
  };
  for (const s of sf.statements) {
    if (ts.isImportDeclaration(s) || ts.isInterfaceDeclaration(s) || ts.isTypeAliasDeclaration(s) || isForwardingStateHook(sf, s) || isStaticDeclaration(sf, s)) continue;
    if (s === component) continue;
    if (ts.isVariableStatement(s) && s.declarationList.declarations.length === 1 && owns(s, component)) continue;
    fail(sf, s, "module-level executable code outside the mounted component is not modeled");
  }
  const namedHooks = new Set();
  const reactObjects = new Set();
  const customHooks = new Map();
  for (const s of sf.statements) {
    if (!ts.isImportDeclaration(s) || !ts.isStringLiteralLike(s.moduleSpecifier)) continue;
    if (s.moduleSpecifier.text.endsWith(".css")) {
      const importedPath = require("node:path").posix.normalize(require("node:path").posix.join(require("node:path").posix.dirname(path), s.moduleSpecifier.text));
      if (!files.has(importedPath)) fail(sf, s, `stylesheet '${s.moduleSpecifier.text}' is outside the source closure`);
      continue;
    }
    if (s.moduleSpecifier.text !== "react") {
      const importedPath = s.moduleSpecifier.text.startsWith(".") ? resolveModule(path, s.moduleSpecifier.text) : null;
      if (!importedPath || !s.importClause || !safeComponentModule(importedPath)) fail(sf, s, `import '${s.moduleSpecifier.text}' has module effects outside the source UI model`);
      if (s.importClause.namedBindings && ts.isNamedImports(s.importClause.namedBindings)) {
        for (const item of s.importClause.namedBindings.elements) {
          const localName = item.name.text;
          const exportedName = (item.propertyName || item.name).text;
          const hook = /^use[A-Z]/.test(localName) && !item.isTypeOnly && resolveForwardingStateHook(importedPath, exportedName);
          if (hook) customHooks.set(localName, hook);
        }
      }
      continue;
    }
    const clause = s.importClause;
    if (!clause) continue;
    if (clause.name) reactObjects.add(clause.name.text);
    if (clause.namedBindings && ts.isNamespaceImport(clause.namedBindings)) reactObjects.add(clause.namedBindings.name.text);
    if (clause.namedBindings && ts.isNamedImports(clause.namedBindings)) {
      for (const specifier of clause.namedBindings.elements) {
        const imported = (specifier.propertyName || specifier.name).text;
        if (/^use[A-Z]/.test(imported) && imported !== "useState") fail(sf, specifier, `React hook '${imported}' is outside the source UI model`);
        if (imported === "useState") namedHooks.add(specifier.name.text);
      }
    }
  }
  const shadows = new Set();
  const bindingNames = (name) => {
    if (ts.isIdentifier(name)) shadows.add(name.text);
    else if (ts.isObjectBindingPattern(name) || ts.isArrayBindingPattern(name)) for (const e of name.elements) if (e && ts.isBindingElement(e)) bindingNames(e.name);
  };
  for (const p of component.parameters) bindingNames(p.name);
  for (const s of component.body && ts.isBlock(component.body) ? component.body.statements : []) {
    if (ts.isVariableStatement(s)) for (const d of s.declarationList.declarations) bindingNames(d.name);
    else if ((ts.isFunctionDeclaration(s) || ts.isClassDeclaration(s)) && s.name) shadows.add(s.name.text);
  }
  const isImportedStateHook = (call) => {
    if (ts.isIdentifier(call.expression)) return namedHooks.has(call.expression.text);
    if (ts.isPropertyAccessExpression(call.expression) && call.expression.name.text === "useState" && ts.isIdentifier(call.expression.expression)) {
      return reactObjects.has(call.expression.expression.text);
    }
    return false;
  };
  const isHook = (call) => {
    const binding = ts.isIdentifier(call.expression) ? call.expression.text : ts.isPropertyAccessExpression(call.expression) && ts.isIdentifier(call.expression.expression) ? call.expression.expression.text : "";
    return isImportedStateHook(call) && !shadows.has(binding);
  };
  const states = new Map();
  const setters = new Map();
  const modeledHooks = new Set();
  const localFns = new Map();
  const body = component.body;
  if (!body || !ts.isBlock(body)) fail(sf, component, "component must use a block body");
  for (const s of body.statements) {
    if (ts.isFunctionDeclaration(s) && s.name) localFns.set(s.name.text, s);
    if (!ts.isVariableStatement(s)) continue;
    for (const d of s.declarationList.declarations) {
      const init = d.initializer && strip(d.initializer);
      if (ts.isIdentifier(d.name) && (s.declarationList.flags & ts.NodeFlags.Const) && init && (ts.isArrowFunction(init) || ts.isFunctionExpression(init))) localFns.set(d.name.text, init);
      if (init && ts.isCallExpression(init) && ts.isIdentifier(init.expression) && init.expression.text === "useEffect") fail(sf, init, "React effects are outside the source UI model");
      if (!ts.isArrayBindingPattern(d.name) || !init || !ts.isCallExpression(init)) {
        if (init && ts.isCallExpression(init)) fail(sf, init, "component initializer calls an unmodeled function");
        continue;
      }
      const directState = isHook(init);
      let initialArg = init.arguments[0];
      if (!directState) {
        const hookBinding = ts.isIdentifier(init.expression) ? init.expression.text : ts.isPropertyAccessExpression(init.expression) && ts.isIdentifier(init.expression.expression) ? init.expression.expression.text : "";
        if (isImportedStateHook(init) && shadows.has(hookBinding)) fail(sf, init, "state initializer call does not resolve to an unshadowed React useState import");
        const custom = !shadows.has(init.expression.text) && (customHooks.get(init.expression.text) || findForwardingStateHook(sf, init.expression.text, false));
        if (!custom || init.arguments.length !== 1) fail(sf, init, "state initializer call does not resolve to React useState or a pure forwarding state hook");
        initialArg = literal(init.arguments[0], sf) ? init.arguments[0] : null;
        if (!initialArg) fail(sf, init.arguments[0] || init, "forwarding state hook needs one finite literal initializer");
      }
      modeledHooks.add(init);
      const [value, set] = d.name.elements;
      if (!value || !ts.isIdentifier(value.name) || (set && !ts.isIdentifier(set.name)) || !initialArg) fail(sf, d, "state hook must bind a named state and setter with an explicit initial value");
      const initial = literal(initialArg, sf);
      if (!initial) fail(sf, initialArg, "state initializer is not a finite boolean, number, string, or null literal");
      const bindings = new Set([...states.keys(), ...setters.keys()]);
      if (bindings.has(value.name.text) || (set && (bindings.has(set.name.text) || value.name.text === set.name.text))) fail(sf, d, "state and setter bindings must be unique in the component");
      const stateName = `${statePrefix}${value.name.text}`;
      states.set(value.name.text, { name: stateName, setter: set ? set.name.text : null, initial: initial[1], line: lineOf(sf, value), owner: statePrefix || null });
      if (set) setters.set(set.name.text, stateName);
    }
  }
  for (const s of body.statements) {
    if (ts.isExpressionStatement(s)) {
      const e = strip(s.expression);
      if (ts.isCallExpression(e) && ts.isIdentifier(e.expression) && /^use[A-Z]/.test(e.expression.text)) fail(sf, e, `hook '${e.expression.text}' has effects outside the source UI model`);
      fail(sf, s, "component has a top-level effect outside the source UI model");
    }
  }

  const stateNames = new Set(states.keys());
  const inspectHooks = (n) => {
    if (n !== component && ts.isFunctionLike(n)) return;
    if (ts.isCallExpression(n)) {
      const called = ts.isIdentifier(n.expression) ? n.expression.text : ts.isPropertyAccessExpression(n.expression) ? n.expression.name.text : "";
      if (/^use[A-Z]/.test(called) && !modeledHooks.has(n)) fail(sf, n, `hook '${called}' is outside the source UI model`);
    }
    ts.forEachChild(n, inspectHooks);
  };
  inspectHooks(component);
  const substitutions = new Map([...componentProps.values]);
  for (const s of sf.statements) if (isStaticDeclaration(sf, s)) {
    for (const d of s.declarationList.declarations) substitutions.set(d.name.text, ["lit", staticValue(d.initializer, sf)]);
  }
  const enc = (e, locals) => expr(e, sf, stateNames, locals, substitutions, statePrefix);
  for (const s of body.statements) {
    if (!ts.isVariableStatement(s)) continue;
    for (const d of s.declarationList.declarations) {
      const init = d.initializer && strip(d.initializer);
      if (!init || modeledHooks.has(init) || ts.isArrowFunction(init) || ts.isFunctionExpression(init)) continue;
      if (ts.isIdentifier(d.name) && (s.declarationList.flags & ts.NodeFlags.Const)) {
        const staticValueResult = staticValue(init, sf);
        if (staticValueResult !== invalidStatic) { substitutions.set(d.name.text, ["lit", staticValueResult]); continue; }
      }
      const value = enc(init, new Set());
      if (ts.isIdentifier(d.name) && (s.declarationList.flags & ts.NodeFlags.Const)) substitutions.set(d.name.text, value);
    }
  }
  const containsJsx = (n) => {
    let found = false;
    const walk = (x) => { if (found) return; if (ts.isJsxElement(x) || ts.isJsxSelfClosingElement(x) || ts.isJsxFragment(x)) found = true; else ts.forEachChild(x, walk); };
    walk(n);
    return found;
  };
  const statement = (st, localVars = new Set()) => {
    if (ts.isBlock(st)) return ["seq", ...st.statements.map((x) => statement(x, localVars))];
    if (ts.isIfStatement(st)) return ["if", enc(st.expression, localVars), statement(st.thenStatement, localVars), st.elseStatement ? statement(st.elseStatement, localVars) : ["seq"]];
    if (ts.isEmptyStatement(st)) return ["seq"];
    if (ts.isReturnStatement(st)) {
      if (st.expression) fail(sf, st, "event handler returns a value");
      return ["return"];
    }
    if (!ts.isExpressionStatement(st)) fail(sf, st, "event handler contains an unmodeled statement");
    const e = strip(st.expression);
    if (ts.isConditionalExpression(e)) return ["if", enc(e.condition, localVars), statement(ts.factory.createExpressionStatement(e.whenTrue), localVars), statement(ts.factory.createExpressionStatement(e.whenFalse), localVars)];
    if (ts.isCallExpression(e) && ts.isIdentifier(e.expression) && componentProps.handlers.has(e.expression.text) && e.arguments.length === 0) return ["invoke", componentProps.handlers.get(e.expression.text)];
    if (!ts.isCallExpression(e) || !ts.isIdentifier(e.expression) || !setters.has(e.expression.text) || e.arguments.length !== 1) fail(sf, e, "event handler performs an effect other than a useState update");
    const stateName = setters.get(e.expression.text);
    const arg = strip(e.arguments[0]);
    let update;
    if (ts.isArrowFunction(arg) || ts.isFunctionExpression(arg)) {
      if (arg.parameters.length !== 1 || !ts.isIdentifier(arg.parameters[0].name) || !ts.isExpression(arg.body)) fail(sf, arg, "functional state update must be a single expression");
      update = ["functional", arg.parameters[0].name.text, enc(arg.body, new Set([arg.parameters[0].name.text]))];
    } else update = ["value", enc(arg, localVars)];
    return ["set", stateName, update, lineOf(sf, e)];
  };

  const handler = (e) => {
    e = strip(e);
    if (ts.isArrowFunction(e) || ts.isFunctionExpression(e)) {
      if (e.parameters.length > 1 || e.parameters.some((p) => !ts.isIdentifier(p.name))) fail(sf, e, "event handler parameters are outside the source UI model");
      const params = new Set(e.parameters.map((p) => p.name.text));
      const usesParam = (node) => {
        if (ts.isIdentifier(node) && params.has(node.text)) return true;
        let found = false;
        ts.forEachChild(node, (child) => { if (usesParam(child)) found = true; });
        return found;
      };
      if (params.size && usesParam(e.body)) fail(sf, e, "event handler reads its browser event parameter; event values are outside the source UI model");
      if (ts.isBlock(e.body)) return statement(e.body);
      return statement(ts.factory.createExpressionStatement(e.body));
    }
    if (ts.isIdentifier(e) && componentProps.handlers.has(e.text)) return componentProps.handlers.get(e.text);
    if (ts.isIdentifier(e) && localFns.has(e.text)) {
      const fn = localFns.get(e.text);
      if (fn.parameters.length > 1 || fn.parameters.some((p) => !ts.isIdentifier(p.name))) fail(sf, fn, "event handler parameters are outside the source UI model");
      if (fn.parameters.length) {
        const param = fn.parameters[0].name.text;
        const uses = (node) => {
          if (ts.isIdentifier(node) && node.text === param) return true;
          let found = false;
          ts.forEachChild(node, (child) => { if (uses(child)) found = true; });
          return found;
        };
        if (uses(fn.body)) fail(sf, fn, "event handler reads its browser event parameter; event values are outside the source UI model");
      }
      return ts.isBlock(fn.body) ? statement(fn.body) : statement(ts.factory.createExpressionStatement(fn.body));
    }
    fail(sf, e, "event handler is not defined in this component");
  };

  const childStates = [];
  let componentInstance = 0;
  let renderedStatefulChildren = 0;
  const render = (e, conditionalMount = false) => {
    e = strip(e);
    if (e.kind === ts.SyntaxKind.NullKeyword || e.kind === ts.SyntaxKind.FalseKeyword) return { type: "empty" };
    if (ts.isJsxElement(e)) return componentElement(e.openingElement, e.children, e, conditionalMount) || element(e.openingElement, e.children, e, conditionalMount);
    if (ts.isJsxSelfClosingElement(e)) return componentElement(e, [], e, conditionalMount) || element(e, [], e, conditionalMount);
    if (ts.isIdentifier(e) && e.text === "children" && componentProps.children) {
      if (componentProps.children.stateful && ++renderedStatefulChildren > 1) fail(sf, e, "stateful children are rendered more than once by a composed component");
      return componentProps.children;
    }
    if (ts.isJsxFragment(e)) return { type: "group", children: e.children.map((c) => render(c, conditionalMount)) };
    if (ts.isParenthesizedExpression(e)) return render(e.expression, conditionalMount);
    if (ts.isCallExpression(e) && ts.isPropertyAccessExpression(e.expression) && e.expression.name.text === "map") return renderStaticMap(e, conditionalMount);
    if (containsJsx(e) && ts.isConditionalExpression(e)) return { type: "branch", test: enc(e.condition, new Set()), yes: render(e.whenTrue, true), no: render(e.whenFalse, true) };
    if (containsJsx(e) && ts.isBinaryExpression(e) && e.operatorToken.kind === ts.SyntaxKind.AmpersandAmpersandToken) return { type: "branch", test: enc(e.left, new Set()), yes: render(e.right, true), no: { type: "text", value: enc(e.left, new Set()) } };
    if (ts.isArrayLiteralExpression(e)) return { type: "group", children: e.elements.map((c) => render(c, conditionalMount)) };
    return { type: "text", value: enc(e, new Set()) };
  };

  function renderStaticMap(call, conditionalMount) {
    if (call.arguments.length !== 1) fail(sf, call, "static UI map needs one source-defined callback");
    const callback = strip(call.arguments[0]);
    if ((!ts.isArrowFunction(callback) && !ts.isFunctionExpression(callback)) || callback.parameters.length !== 1 || !ts.isExpression(callback.body)) fail(sf, callback, "static UI map callback must be one expression over one item");
    const sourceExpr = strip(call.expression.expression);
    let sourceValue = staticValue(sourceExpr, sf);
    if (ts.isIdentifier(sourceExpr) && substitutions.has(sourceExpr.text)) {
      const replacement = substitutions.get(sourceExpr.text);
      if (replacement[0] === "lit") sourceValue = replacement[1];
    }
    if (!Array.isArray(sourceValue)) fail(sf, sourceExpr, "UI map source must be an immutable literal array");
    const parameter = callback.parameters[0].name;
    let names = [];
    if (ts.isIdentifier(parameter)) names = [parameter.text];
    else if (ts.isArrayBindingPattern(parameter) && parameter.elements.every((item) => ts.isBindingElement(item) && ts.isIdentifier(item.name) && !item.initializer && !item.dotDotDotToken)) names = parameter.elements.map((item) => item.name.text);
    else fail(sf, callback.parameters[0], "static UI map callback needs an identifier or simple tuple parameter");
    if (names.some((name) => stateNames.has(name) || substitutions.has(name))) fail(sf, callback.parameters[0], "static UI map parameter shadows a source state or constant");
    const rendered = [];
    for (const item of sourceValue) {
      const values = ts.isIdentifier(parameter) ? [item] : Array.isArray(item) ? item : null;
      if (!values || values.length !== names.length) fail(sf, callback, "static UI map item does not match its callback parameter");
      const previous = names.map((name) => [name, substitutions.has(name), substitutions.get(name)]);
      names.forEach((name, index) => substitutions.set(name, ["lit", values[index]]));
      try { rendered.push(render(callback.body, conditionalMount)); }
      finally {
        for (const [name, hadValue, oldValue] of previous) {
          if (hadValue) substitutions.set(name, oldValue);
          else substitutions.delete(name);
        }
      }
    }
    return { type: "group", children: rendered };
  }

  function componentElement(open, children, whole, conditionalMount) {
    if (!ts.isIdentifier(open.tagName) || !/^[A-Z]/.test(open.tagName.text)) return null;
    const target = resolveComponent(path, sf, open.tagName.text, component);
    if (!target) fail(sf, open.tagName, `composed component '${open.tagName.text}' is not defined in the source module closure`);
    const values = new Map();
    const handlers = new Map();
    for (const a of open.attributes.properties) {
      if (!ts.isJsxAttribute(a) || !ts.isIdentifier(a.name)) fail(sf, a, "composed component spreads and namespaced props are outside the source UI model");
      const name = a.name.text;
      if (!a.initializer) { values.set(name, ["lit", true]); continue; }
      if (ts.isStringLiteral(a.initializer)) { values.set(name, ["jsx-lit", a.initializer.text]); continue; }
      if (!ts.isJsxExpression(a.initializer) || !a.initializer.expression) fail(sf, a, `composed component prop '${name}' is outside the source UI model`);
      if (/^on[A-Z]/.test(name)) handlers.set(name, handler(a.initializer.expression));
      else values.set(name, enc(a.initializer.expression, new Set()));
    }
    const childStateStart = childStates.length;
    const childTree = { type: "group", children: jsxChildren(children, conditionalMount) };
    childTree.stateful = childStates.length > childStateStart;
    const instancePrefix = `${statePrefix}${target.path}@${componentInstance++}/`;
    const nested = scanComponent(target.path, target.text, target.sf, target.node, true, { values, handlers, children: childTree }, instancePrefix, conditionalMount);
    if (nested.states.length && values.has("key")) fail(sf, whole, `stateful child component '${open.tagName.text}' uses a React key whose identity changes are outside the source UI model`);
    childStates.push(...nested.states);
    return { type: "component", id: instancePrefix, line: lineOf(sf, whole), componentPath: target.path, stateful: nested.states.length > 0, child: nested.render };
  }

  function element(open, children, whole, conditionalMount) {
    const tag = open.tagName.getText(sf);
    if (!/^[a-z][a-z0-9-]*$/.test(tag)) fail(sf, open.tagName, `composed component '${tag}' is not yet modeled`);
    if (["a", "input", "textarea", "select", "form", "fieldset", "details", "summary", "dialog", "style", "script", "link"].includes(tag)) fail(sf, open.tagName, `native ${tag} behavior is outside the source UI model`);
    if (!modeledTags.has(tag)) fail(sf, open.tagName, `native ${tag} accessibility semantics are outside the source UI model`);
    const props = {};
    const events = {};
    for (const a of open.attributes.properties) {
      if (!ts.isJsxAttribute(a)) fail(sf, a, "spread JSX attributes are outside the source UI model");
      const name = a.name.getText(sf);
      if (name === "key") continue;
      if (name === "style") fail(sf, a, "inline style objects are outside the source UI model");
      if (name === "value" || name === "checked") fail(sf, a, `native ${name} semantics are outside the source UI model`);
      if (name === "role" && !["div", "span"].includes(tag)) fail(sf, a, `role override on native ${tag} is outside the source UI model`);
      if (["inert", "popover", "popovertarget", "contenteditable"].includes(name.toLowerCase())) fail(sf, a, `native ${name} behavior is outside the source UI model`);
      if (name.startsWith("aria-") && !modeledAria.has(name.toLowerCase())) fail(sf, a, `ARIA attribute '${name}' changes behavior outside the source UI model`);
      if (!a.initializer) { props[name] = ["lit", true]; continue; }
      if (ts.isStringLiteral(a.initializer)) props[name] = ["jsx-lit", a.initializer.text];
      else if (ts.isJsxExpression(a.initializer) && a.initializer.expression) {
        if (name === "onClick") events.click = handler(a.initializer.expression);
        else if (/^on[A-Z]/.test(name)) fail(sf, a, `event '${name}' is outside the source UI model`);
        else props[name] = enc(a.initializer.expression, new Set());
      } else fail(sf, a, `attribute '${name}' is outside the source UI model`);
    }
    return { type: "element", tag, line: lineOf(sf, whole), props, events, children: jsxChildren(children, conditionalMount) };
  }

  function jsxChildren(children, conditionalMount) {
    return children.map((c) => ts.isJsxText(c) ? { type: "jsxText", value: jsxText(c.text) } : ts.isJsxExpression(c) ? c.expression ? render(c.expression, conditionalMount) : { type: "empty" } : ts.isJsxElement(c) || ts.isJsxSelfClosingElement(c) || ts.isJsxFragment(c) ? render(c, conditionalMount) : (fail(sf, c, "JSX child is outside the source UI model"), { type: "empty" }));
  }

  const renderFlow = (statements, allowFallthrough = false, conditionalMount = false) => {
    statements = statements.filter((s) => !ts.isEmptyStatement(s));
    if (!statements.length) {
      if (allowFallthrough) return { type: "empty" };
      fail(sf, component, "component control flow can fall through without rendering");
    }
    const [first, ...rest] = statements;
    if (ts.isReturnStatement(first)) {
      if (!first.expression) fail(sf, first, "component return has no render expression");
      if (rest.length) fail(sf, rest[0], "component has executable code after an unconditional return");
      return render(first.expression, conditionalMount);
    }
    if (ts.isIfStatement(first)) {
      const yes = renderFlow(ts.isBlock(first.thenStatement) ? first.thenStatement.statements : [first.thenStatement], false, true);
      const noStatements = first.elseStatement ? (ts.isBlock(first.elseStatement) ? first.elseStatement.statements : [first.elseStatement]) : rest;
      const no = renderFlow(noStatements, !first.elseStatement, true);
      if (first.elseStatement && rest.length) fail(sf, rest[0], "component control flow after a returning branch is not modeled");
      return { type: "branch", test: enc(first.expression, new Set()), yes, no };
    }
    fail(sf, first, "component control flow before render is outside the source UI model");
  };
  for (const [name, d] of states) {
    for (const v of body.statements) {
      if (ts.isExpressionStatement(v) && ts.isCallExpression(strip(v.expression)) && ts.isIdentifier(strip(v.expression).expression) && strip(v.expression).expression.text === d.setter) fail(sf, v, "state update occurs outside an event handler");
    }
  }
  const renderTree = renderFlow(body.statements.filter((s) => !(ts.isVariableStatement(s) || ts.isFunctionDeclaration(s))), false, dynamicMount);
  const statefulComponents = (node, into = new Set()) => {
    if (!node || typeof node !== "object") return into;
    if (node.type === "component" && node.stateful) into.add(node.componentPath);
    if (node.type === "branch") {
      const yes = statefulComponents(node.yes);
      const no = statefulComponents(node.no);
      if ([...yes].some((name) => no.has(name))) fail(sf, component, "conditional branches reuse a stateful component type whose React instance identity is outside the source model");
      for (const name of yes) into.add(name);
      for (const name of no) into.add(name);
    } else if (node.type === "component") statefulComponents(node.child, into);
    else if (node.children) for (const child of node.children) statefulComponents(child, into);
    return into;
  };
  statefulComponents(renderTree);
  return { path, component: component.name ? component.name.text : "default", line: lineOf(sf, component), states: [...states.values(), ...childStates], render: renderTree };
}

function componentCandidates(path, text) {
  const kind = /\.(tsx|jsx)$/.test(path) ? ts.ScriptKind.TSX : /\.(jsx|js|mjs|cjs)$/.test(path) ? ts.ScriptKind.JSX : ts.ScriptKind.TS;
  const sf = ts.createSourceFile(path, text, ts.ScriptTarget.Latest, true, kind);
  const out = [];
  const find = (n) => {
    if ((ts.isFunctionDeclaration(n) || ts.isArrowFunction(n) || ts.isFunctionExpression(n)) && n.body) {
      let found = false;
      const jsx = (x) => { if (ts.isJsxElement(x) || ts.isJsxSelfClosingElement(x) || ts.isJsxFragment(x)) found = true; else ts.forEachChild(x, jsx); };
      jsx(n.body);
      if (found) out.push({ sf, node: n, name: n.name && n.name.text || (n.parent && ts.isVariableDeclaration(n.parent) && ts.isIdentifier(n.parent.name) ? n.parent.name.text : "default") });
      return;
    }
    ts.forEachChild(n, find);
  };
  find(sf);
  return out;
}

function resolveNamedExport(path, exportName, seen = new Set()) {
  const key = `${path}\0${exportName}`;
  if (seen.has(key)) return null;
  seen.add(key);
  const file = files.get(path);
  if (!file) return null;
  const candidates = componentCandidates(path, file.text);
  const direct = candidates.find((candidate) => {
    const own = ts.canHaveModifiers(candidate.node) ? ts.getModifiers(candidate.node) || [] : [];
    const parent = candidate.node.parent;
    const declaration = ts.isVariableDeclaration(parent) && ts.isVariableDeclarationList(parent.parent) && ts.isVariableStatement(parent.parent.parent) ? parent.parent.parent : null;
    const statementMods = declaration && ts.canHaveModifiers(declaration) ? ts.getModifiers(declaration) || [] : [];
    const defaultExport = candidate.name === "default" || [...own, ...statementMods].some((m) => m.kind === ts.SyntaxKind.DefaultKeyword);
    const namedExport = [...own, ...statementMods].some((m) => m.kind === ts.SyntaxKind.ExportKeyword);
    return exportName === "default" ? defaultExport : candidate.name === exportName && namedExport;
  });
  if (direct) return { path, sf: direct.sf, node: direct.node, name: direct.name };
  const kind = /\.(tsx|jsx)$/.test(path) ? ts.ScriptKind.TSX : /\.(jsx|js|mjs|cjs)$/.test(path) ? ts.ScriptKind.JSX : ts.ScriptKind.TS;
  const sf = ts.createSourceFile(path, file.text, ts.ScriptTarget.Latest, true, kind);
  const matches = [];
  for (const statement of sf.statements) {
    if (!ts.isExportDeclaration(statement) || !ts.isStringLiteralLike(statement.moduleSpecifier)) continue;
    const resolved = resolveModule(path, statement.moduleSpecifier.text);
    if (!resolved) continue;
    if (statement.exportClause && ts.isNamedExports(statement.exportClause)) {
      for (const item of statement.exportClause.elements) {
        if (item.name.text !== exportName || item.isTypeOnly) continue;
        matches.push(resolveNamedExport(resolved, (item.propertyName || item.name).text, seen));
      }
    } else if (!statement.exportClause && exportName !== "default") {
      matches.push(resolveNamedExport(resolved, exportName, seen));
    }
  }
  const found = matches.filter(Boolean);
  return found.length === 1 ? found[0] : null;
}

function isStaticDeclaration(sf, statement) {
  return ts.isVariableStatement(statement) && (statement.declarationList.flags & ts.NodeFlags.Const)
    && statement.declarationList.declarations.length > 0
    && statement.declarationList.declarations.every((d) => ts.isIdentifier(d.name) && d.initializer && staticValue(d.initializer, sf) !== invalidStatic);
}

function findForwardingStateHook(sf, name, requireExport) {
  let node = null;
  let exported = false;
  for (const s of sf.statements) {
    if (ts.isFunctionDeclaration(s) && s.name?.text === name) {
      node = s;
      exported = (ts.getModifiers(s) || []).some((m) => m.kind === ts.SyntaxKind.ExportKeyword);
    }
    if (ts.isVariableStatement(s)) for (const d of s.declarationList.declarations) {
      const init = d.initializer && strip(d.initializer);
      if (ts.isIdentifier(d.name) && d.name.text === name && init && (ts.isArrowFunction(init) || ts.isFunctionExpression(init))) {
        node = init;
        exported = (ts.getModifiers(s) || []).some((m) => m.kind === ts.SyntaxKind.ExportKeyword);
      }
    }
  }
  if (!node || requireExport && !exported || !/^use[A-Z]/.test(name) || node.parameters.length !== 1 || !ts.isIdentifier(node.parameters[0].name) || node.parameters[0].initializer || !node.body || !ts.isBlock(node.body)) return null;
  const statements = node.body.statements;
  if (statements.length !== 2 || !ts.isVariableStatement(statements[0]) || !ts.isReturnStatement(statements[1])) return null;
  const decls = statements[0].declarationList.declarations;
  if (decls.length !== 1 || !ts.isArrayBindingPattern(decls[0].name) || decls[0].name.elements.length !== 2) return null;
  const [state, setter] = decls[0].name.elements;
  const call = decls[0].initializer && strip(decls[0].initializer);
  if (!ts.isBindingElement(state) || !ts.isIdentifier(state.name) || !ts.isBindingElement(setter) || !ts.isIdentifier(setter.name)
      || !ts.isCallExpression(call) || call.arguments.length !== 1 || !ts.isIdentifier(call.arguments[0]) || call.arguments[0].text !== node.parameters[0].name.text) return null;
  let useStateNames = new Set();
  let reactObjects = new Set();
  for (const s of sf.statements) {
    if (!ts.isImportDeclaration(s) || s.moduleSpecifier.text !== "react" || !s.importClause) continue;
    if (s.importClause.name) reactObjects.add(s.importClause.name.text);
    if (s.importClause.namedBindings && ts.isNamespaceImport(s.importClause.namedBindings)) reactObjects.add(s.importClause.namedBindings.name.text);
    if (s.importClause.namedBindings && ts.isNamedImports(s.importClause.namedBindings)) for (const i of s.importClause.namedBindings.elements) {
      if ((i.propertyName || i.name).text === "useState" && !i.isTypeOnly) useStateNames.add(i.name.text);
    }
  }
  const genuine = ts.isIdentifier(call.expression) && useStateNames.has(call.expression.text)
    || ts.isPropertyAccessExpression(call.expression) && call.expression.name.text === "useState" && ts.isIdentifier(call.expression.expression) && reactObjects.has(call.expression.expression.text);
  if (!genuine || useStateNames.has(node.parameters[0].name.text) || reactObjects.has(node.parameters[0].name.text)
      || useStateNames.has(state.name.text) || useStateNames.has(setter.name.text) || reactObjects.has(state.name.text) || reactObjects.has(setter.name.text)) return null;
  const result = strip(statements[1].expression);
  if (!result || !ts.isArrayLiteralExpression(result) || result.elements.length !== 2 || !ts.isIdentifier(result.elements[0]) || !ts.isIdentifier(result.elements[1])
      || result.elements[0].text !== state.name.text || result.elements[1].text !== setter.name.text) return null;
  return { initial: node.parameters[0].name.text };
}

function isForwardingStateHook(sf, statement) {
  if (ts.isFunctionDeclaration(statement) && statement.name) return !!findForwardingStateHook(sf, statement.name.text, false);
  if (ts.isVariableStatement(statement)) return statement.declarationList.declarations.some((d) => ts.isIdentifier(d.name) && findForwardingStateHook(sf, d.name.text, false));
  return false;
}

function resolveForwardingStateHook(path, exportName, seen = new Set()) {
  const key = `${path}\0${exportName}`;
  if (seen.has(key)) return null;
  seen.add(key);
  const file = files.get(path);
  if (!file) return null;
  const kind = /\.(tsx|jsx)$/.test(path) ? ts.ScriptKind.TSX : /\.(jsx|js|mjs|cjs)$/.test(path) ? ts.ScriptKind.JSX : ts.ScriptKind.TS;
  const sf = ts.createSourceFile(path, file.text, ts.ScriptTarget.Latest, true, kind);
  const direct = findForwardingStateHook(sf, exportName, true);
  if (direct) return direct;
  const matches = [];
  for (const statement of sf.statements) {
    if (!ts.isExportDeclaration(statement)) continue;
    if (ts.isStringLiteralLike(statement.moduleSpecifier)) {
      const resolved = resolveModule(path, statement.moduleSpecifier.text);
      if (!resolved) continue;
      if (statement.exportClause && ts.isNamedExports(statement.exportClause)) {
        for (const item of statement.exportClause.elements) {
          if (item.name.text === exportName && !item.isTypeOnly) matches.push(resolveForwardingStateHook(resolved, (item.propertyName || item.name).text, seen));
        }
      } else if (!statement.exportClause && exportName !== "default") {
        matches.push(resolveForwardingStateHook(resolved, exportName, seen));
      }
    } else if (statement.exportClause && ts.isNamedExports(statement.exportClause)) {
      for (const item of statement.exportClause.elements) {
        if (item.name.text === exportName && !item.isTypeOnly) {
          const localName = (item.propertyName || item.name).text;
          const hook = findForwardingStateHook(sf, localName, false);
          if (hook) matches.push(hook);
        }
      }
    }
  }
  const found = matches.filter(Boolean);
  return found.length === 1 ? found[0] : null;
}

function resolveModule(fromPath, specifier) {
  const path = resolutions[`${fromPath}\0${specifier}`];
  if (typeof path === "string" && files.has(path)) return path;
  if (input.pipeline === "vite-react") return null;
  const base = require("node:path").posix.normalize(require("node:path").posix.join(require("node:path").posix.dirname(fromPath), specifier));
  const candidates = /\.[cm]?[jt]sx?$/.test(base) ? [base] : [base, ...[".tsx", ".ts", ".jsx", ".js", ".mts", ".mjs", ".cts", ".cjs"].map((ext) => base + ext), ...["index.tsx", "index.ts", "index.jsx", "index.js"].map((name) => `${base}/${name}`)];
  return candidates.find((candidate) => files.has(candidate)) || null;
}

function safeComponentModule(path, seen = new Set()) {
  if (seen.has(path)) return true;
  seen.add(path);
  const file = files.get(path);
  if (!file) return false;
  const kind = /\.(tsx|jsx)$/.test(path) ? ts.ScriptKind.TSX : /\.(jsx|js|mjs|cjs)$/.test(path) ? ts.ScriptKind.JSX : ts.ScriptKind.TS;
  const sf = ts.createSourceFile(path, file.text, ts.ScriptTarget.Latest, true, kind);
  for (const s of sf.statements) {
      if ((ts.isImportDeclaration(s) || ts.isExportDeclaration(s)) && ts.isStringLiteralLike(s.moduleSpecifier)) {
        const from = s.moduleSpecifier.text;
        if (from === "react") continue;
        if (from.endsWith(".css")) {
          if (ts.isExportDeclaration(s)) return false;
          const css = require("node:path").posix.normalize(require("node:path").posix.join(require("node:path").posix.dirname(path), from));
          if (!files.has(css)) return false;
          continue;
        }
        const importedPath = from.startsWith(".") && resolveModule(path, from);
        if (!importedPath || ts.isImportDeclaration(s) && !s.importClause || !safeComponentModule(importedPath, seen)) return false;
        continue;
      }
    if (ts.isFunctionDeclaration(s) || ts.isInterfaceDeclaration(s) || ts.isTypeAliasDeclaration(s) || ts.isExportDeclaration(s)) continue;
    if (ts.isExpressionStatement(s) && ts.isStringLiteral(s.expression)) continue;
    if (isStaticDeclaration(sf, s) || ts.isVariableStatement(s) && s.declarationList.declarations.every((d) => d.initializer && (ts.isArrowFunction(strip(d.initializer)) || ts.isFunctionExpression(strip(d.initializer))))) continue;
    return false;
  }
  return true;
}

function resolveComponent(fromPath, sf, name, current) {
  const local = componentCandidates(fromPath, sf.text).find((c) => c.name === name && c.node !== current);
  if (local) return { path: fromPath, text: sf.text, sf: local.sf, node: local.node };
  for (const s of sf.statements) {
    if (!ts.isImportDeclaration(s) || !ts.isStringLiteralLike(s.moduleSpecifier) || !s.moduleSpecifier.text.startsWith(".")) continue;
    const clause = s.importClause;
    if (!clause) continue;
    const resolved = resolveModule(fromPath, s.moduleSpecifier.text);
    if (!resolved) continue;
    const imported = [];
    if (clause.name && clause.name.text === name) imported.push({ source: "default", exported: true });
    if (clause.namedBindings && ts.isNamedImports(clause.namedBindings)) {
      for (const item of clause.namedBindings.elements) {
        if (item.name.text === name) imported.push({ source: (item.propertyName || item.name).text, exported: !item.isTypeOnly });
      }
    }
    for (const binding of imported) {
      if (!binding.exported) continue;
      const match = resolveNamedExport(resolved, binding.source);
      if (match) return { path: match.path, text: files.get(match.path).text, sf: match.sf, node: match.node };
    }
  }
  return null;
}

function mountedComponent(target, files) {
  const rootLookup = (e) => {
    e = strip(e);
    if (!ts.isCallExpression(e) || !ts.isPropertyAccessExpression(e.expression) || !ts.isIdentifier(e.expression.expression) || e.expression.expression.text !== "document" || e.arguments.length !== 1 || !ts.isStringLiteralLike(e.arguments[0])) return false;
    if (e.expression.name.text === "getElementById") return e.arguments[0].text.length > 0 ? e.arguments[0].text : false;
    const match = e.expression.name.text === "querySelector" && e.arguments[0].text.match(/^#([A-Za-z_][\w-]*)$/);
    return match ? match[1] : false;
  };
  for (const f of files) {
    const kind = /\.(tsx|jsx)$/.test(f.path) ? ts.ScriptKind.TSX : /\.(jsx|js|mjs|cjs)$/.test(f.path) ? ts.ScriptKind.JSX : ts.ScriptKind.TS;
    const sf = ts.createSourceFile(f.path, f.text, ts.ScriptTarget.Latest, true, kind);
    const roots = new Set();
    let targetBinding = null;
    let importsOnlyExpected = true;
    for (const s of sf.statements) {
      if (!ts.isImportDeclaration(s) || !ts.isStringLiteralLike(s.moduleSpecifier)) continue;
      const from = s.moduleSpecifier.text;
      const clause = s.importClause;
      if (from === "react-dom/client" && clause?.namedBindings && ts.isNamedImports(clause.namedBindings)) {
        for (const item of clause.namedBindings.elements) if ((item.propertyName || item.name).text === "createRoot") roots.add(item.name.text);
      } else if (from.startsWith(".")) {
        const importedPath = resolveModule(f.path, from);
        if (from.endsWith(".css") && importedPath) continue;
        if (importedPath === target.path && clause) {
          if (target.defaultExport && clause.name) targetBinding = clause.name.text;
          if (clause.namedBindings && ts.isNamedImports(clause.namedBindings)) {
            for (const item of clause.namedBindings.elements) if ((item.propertyName || item.name).text === target.name) targetBinding = item.name.text;
          }
        } else importsOnlyExpected = false;
      } else importsOnlyExpected = false;
    }
    if (!importsOnlyExpected || !targetBinding || !roots.size) continue;
    const executable = sf.statements.filter((s) => !ts.isImportDeclaration(s) && !(ts.isExpressionStatement(s) && ts.isStringLiteral(s.expression)));
    if (executable.length !== 1 || !ts.isExpressionStatement(executable[0])) continue;
    const mount = strip(executable[0].expression);
    if (!ts.isCallExpression(mount) || !ts.isPropertyAccessExpression(mount.expression) || mount.expression.name.text !== "render" || mount.arguments.length !== 1) continue;
    const create = strip(mount.expression.expression);
    if (!ts.isCallExpression(create) || !ts.isIdentifier(create.expression) || !roots.has(create.expression.text) || create.arguments.length !== 1) continue;
    const root = rootLookup(create.arguments[0]);
    if (!root) continue;
    const app = strip(mount.arguments[0]);
    const tag = ts.isJsxSelfClosingElement(app) ? app.tagName : ts.isJsxElement(app) ? app.openingElement.tagName : null;
    const attributes = ts.isJsxSelfClosingElement(app) ? app.attributes.properties : ts.isJsxElement(app) ? app.openingElement.attributes.properties : [];
    const children = ts.isJsxElement(app) ? app.children : [];
    if (tag && ts.isIdentifier(tag) && tag.text === targetBinding && attributes.length === 0 && children.length === 0) return { root, entry: f.path };
  }
  return false;
}

const models = [];
const errors = [];
let connected = false;
for (const f of input.files) {
  for (const c of componentCandidates(f.path, f.text)) {
    const ownMods = ts.canHaveModifiers(c.node) ? ts.getModifiers(c.node) || [] : [];
    const parent = c.node.parent;
    const variableStatement = ts.isVariableDeclaration(parent) && ts.isVariableDeclarationList(parent.parent) && ts.isVariableStatement(parent.parent.parent) ? parent.parent.parent : null;
    const exportMods = variableStatement && ts.canHaveModifiers(variableStatement) ? ts.getModifiers(variableStatement) || [] : [];
    const exported = c.name === "default" || ownMods.some((m) => m.kind === ts.SyntaxKind.ExportKeyword) || exportMods.some((m) => m.kind === ts.SyntaxKind.ExportKeyword);
    if (!exported) continue;
    const defaultExport = c.name === "default" || ownMods.some((m) => m.kind === ts.SyntaxKind.DefaultKeyword) || exportMods.some((m) => m.kind === ts.SyntaxKind.DefaultKeyword);
    const mountRoot = mountedComponent({ path: f.path, name: c.name, defaultExport }, input.files);
    if (!mountRoot) continue;
    connected = true;
    try { models.push({ ...scanComponent(f.path, f.text, c.sf, c.node), mountRoot: mountRoot.root, mountEntry: mountRoot.entry }); }
    catch (e) { errors.push(String(e && e.message || e).split("\n")[0]); }
  }
}
if (!connected) errors.push("no exported JSX component is connected to a verified React createRoot(...).render(...) entry");
process.stdout.write(JSON.stringify({ models, errors }));
