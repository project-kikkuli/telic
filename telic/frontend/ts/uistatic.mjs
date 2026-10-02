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

function expr(e, sf, states, locals = new Set(), substitutions = new Map(), statePrefix = "", routeBindings = new Set()) {
  e = strip(e);
  const lit = literal(e, sf);
  if (lit) return lit;
  if (ts.isIdentifier(e)) {
    if (locals.has(e.text)) return ["local", e.text];
    if (states.has(e.text)) return ["state", `${statePrefix}${e.text}`];
    if (substitutions.has(e.text)) return substitutions.get(e.text);
    fail(sf, e, `reads unmodeled value '${e.text}'`);
  }
  if (ts.isPropertyAccessExpression(e)) {
    if (e.name.text === "pathname" && ts.isIdentifier(e.expression) && routeBindings.has(e.expression.text)) return ["route"];
    return ["member", expr(e.expression, sf, states, locals, substitutions, statePrefix, routeBindings), ["lit", e.name.text]];
  }
  if (ts.isElementAccessExpression(e) && e.argumentExpression) return ["member", expr(e.expression, sf, states, locals, substitutions, statePrefix, routeBindings), expr(e.argumentExpression, sf, states, locals, substitutions, statePrefix, routeBindings)];
  if (ts.isPrefixUnaryExpression(e) && [ts.SyntaxKind.ExclamationToken, ts.SyntaxKind.MinusToken, ts.SyntaxKind.PlusToken].includes(e.operator)) {
    const op = e.operator === ts.SyntaxKind.ExclamationToken ? "not" : e.operator === ts.SyntaxKind.MinusToken ? "neg" : "pos";
    return ["un", op, expr(e.operand, sf, states, locals, substitutions, statePrefix, routeBindings)];
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
    return ["bin", op, expr(e.left, sf, states, locals, substitutions, statePrefix, routeBindings), expr(e.right, sf, states, locals, substitutions, statePrefix, routeBindings)];
  }
  if (ts.isConditionalExpression(e)) return ["if", expr(e.condition, sf, states, locals, substitutions, statePrefix, routeBindings), expr(e.whenTrue, sf, states, locals, substitutions, statePrefix, routeBindings), expr(e.whenFalse, sf, states, locals, substitutions, statePrefix, routeBindings)];
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
    if (ts.isImportDeclaration(s) || ts.isInterfaceDeclaration(s) || ts.isTypeAliasDeclaration(s) || isForwardingStateHook(sf, s) || isStaticDeclaration(sf, s) || isContextDeclaration(sf, s) || ts.isFunctionDeclaration(s)) continue;
    if (s === component) continue;
    if (ts.isVariableStatement(s) && s.declarationList.declarations.length === 1 && owns(s, component)) continue;
    fail(sf, s, "module-level executable code outside the mounted component is not modeled");
  }
  const namedHooks = new Set();
  const namedEffectHooks = new Set();
  const reactObjects = new Set();
  const routerHooks = new Map();
  const routerComponents = new Map();
  const routerUses = new Set();
  const customHooks = new Map();
  const contextHooks = new Map();
  for (const s of sf.statements) {
    if (!ts.isImportDeclaration(s) || !ts.isStringLiteralLike(s.moduleSpecifier)) continue;
    if (s.moduleSpecifier.text.endsWith(".css")) {
      const importedPath = require("node:path").posix.normalize(require("node:path").posix.join(require("node:path").posix.dirname(path), s.moduleSpecifier.text));
      if (!files.has(importedPath)) fail(sf, s, `stylesheet '${s.moduleSpecifier.text}' is outside the source closure`);
      continue;
    }
      if (s.moduleSpecifier.text === "react-router-dom") {
        const clause = s.importClause;
        if (clause?.namedBindings && ts.isNamedImports(clause.namedBindings)) {
          for (const specifier of clause.namedBindings.elements) {
            const imported = (specifier.propertyName || specifier.name).text;
            if (specifier.isTypeOnly || clause.isTypeOnly) continue;
            if (["useNavigate", "useLocation"].includes(imported)) routerHooks.set(specifier.name.text, imported);
            if (["Routes", "Route"].includes(imported)) routerComponents.set(specifier.name.text, imported);
          }
        }
        continue;
      }
      if (s.moduleSpecifier.text !== "react") {
      const importedPath = s.moduleSpecifier.text.startsWith(".") ? resolveModule(path, s.moduleSpecifier.text) : null;
      if (!importedPath || !s.importClause || !safeComponentModule(importedPath)) fail(sf, s, `import '${s.moduleSpecifier.text}' has module effects outside the source UI model`);
      if (s.importClause.namedBindings && ts.isNamedImports(s.importClause.namedBindings)) {
        for (const item of s.importClause.namedBindings.elements) {
          const localName = item.name.text;
          const exportedName = (item.propertyName || item.name).text;
          const context = !item.isTypeOnly && !s.importClause.isTypeOnly && /^use[A-Z]/.test(localName) && contextHook(importedPath, exportedName);
          if (context) contextHooks.set(localName, context);
          const hook = /^use[A-Z]/.test(localName) && !item.isTypeOnly && !s.importClause.isTypeOnly && resolveForwardingStateHook(importedPath, exportedName);
          if (hook) customHooks.set(localName, hook);
        }
      }
      continue;
    }
    const clause = s.importClause;
    if (!clause || clause.isTypeOnly) continue;
    if (clause.name) reactObjects.add(clause.name.text);
    if (clause.namedBindings && ts.isNamespaceImport(clause.namedBindings)) reactObjects.add(clause.namedBindings.name.text);
    if (clause.namedBindings && ts.isNamedImports(clause.namedBindings)) {
      for (const specifier of clause.namedBindings.elements) {
        const imported = (specifier.propertyName || specifier.name).text;
        if (/^use[A-Z]/.test(imported) && !["useState", "useContext", "useEffect"].includes(imported) && !specifier.isTypeOnly) fail(sf, specifier, `React hook '${imported}' is outside the source UI model`);
        if (imported === "useState" && !specifier.isTypeOnly && !clause.isTypeOnly) namedHooks.add(specifier.name.text);
        if (imported === "useEffect" && !specifier.isTypeOnly) namedEffectHooks.add(specifier.name.text);
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
  const isEffectHook = (call) => ts.isIdentifier(call.expression) && namedEffectHooks.has(call.expression.text)
    || ts.isPropertyAccessExpression(call.expression) && call.expression.name.text === "useEffect" && ts.isIdentifier(call.expression.expression) && reactObjects.has(call.expression.expression.text);
  const states = new Map();
  const setters = new Map();
  const externalValues = new Map();
  let activeContexts = new Map(componentProps.contexts || []);
  const pendingEffects = [];
  const navigateBindings = new Set();
  const locationBindings = new Set();
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
      if (ts.isIdentifier(d.name) && init && ts.isCallExpression(init) && ts.isIdentifier(init.expression) && routerHooks.has(init.expression.text)) {
        const hook = routerHooks.get(init.expression.text);
        if (hook === "useNavigate" && init.arguments.length === 0) navigateBindings.add(d.name.text);
        else if (hook === "useLocation" && init.arguments.length === 0) locationBindings.add(d.name.text);
        else fail(sf, init, `${hook} call is outside the route model`);
        routerUses.add(hook);
        modeledHooks.add(init);
        continue;
      }
      if (ts.isObjectBindingPattern(d.name) && init && ts.isCallExpression(init) && ts.isIdentifier(init.expression) && contextHooks.has(init.expression.text)) {
        const context = contextHooks.get(init.expression.text).context;
        const fields = activeContexts.get(context);
        if (!fields) fail(sf, init, `custom hook '${init.expression.text}' reads context '${context}' without a mounted provider frame`);
        for (const item of d.name.elements) {
          if (!ts.isBindingElement(item) || item.dotDotDotToken || item.initializer || !ts.isIdentifier(item.name)) fail(sf, item, "context destructuring must bind named fields");
          const field = item.propertyName ? item.propertyName.getText(sf) : item.name.text;
          if (!Object.hasOwn(fields, field)) fail(sf, item, `context value has no field '${field}'`);
          const local = item.name.text;
          const value = fields[field];
          if (value[0] === "setter") setters.set(local, value[1]);
          else externalValues.set(local, value);
        }
        modeledHooks.add(init);
        continue;
      }
      if (init && ts.isCallExpression(init) && isEffectHook(init)) {
        pendingEffects.push({ call: init, line: lineOf(sf, init) });
        modeledHooks.add(init);
        continue;
      }
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
      let initial = literal(initialArg, sf);
      if (!initial && ts.isIdentifier(initialArg)) {
        const value = componentProps.values.get(initialArg.text);
        if (value && ["lit", "jsx-lit"].includes(value[0]) && ["string", "number", "boolean"].includes(typeof value[1])) initial = ["lit", value[1]];
      }
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
      if (ts.isCallExpression(e) && isEffectHook(e)) {
        pendingEffects.push({ call: e, line: lineOf(sf, e) });
        modeledHooks.add(e);
        continue;
      }
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
  const substitutions = new Map([...externalValues, ...componentProps.values]);
  for (const s of sf.statements) if (isStaticDeclaration(sf, s)) {
    for (const d of s.declarationList.declarations) substitutions.set(d.name.text, ["lit", staticValue(d.initializer, sf)]);
  }
  const enc = (e, locals) => expr(e, sf, stateNames, locals, substitutions, statePrefix, locationBindings);
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
    if (ts.isCallExpression(e) && ts.isIdentifier(e.expression) && navigateBindings.has(e.expression.text) && e.arguments.length >= 1 && e.arguments.length <= 2) {
      const destination = strip(e.arguments[0]);
      if (!ts.isStringLiteralLike(destination)) fail(sf, destination || e, "navigation destination must be a literal path");
      if (!destination.text.startsWith("/")) fail(sf, destination, "relative navigation paths are outside the route model");
      if (destination.text.includes("?") || destination.text.includes("#")) fail(sf, destination, "query strings and URL fragments are outside the route model");
      return ["navigate", destination.text];
    }
    if (!ts.isCallExpression(e) || !ts.isIdentifier(e.expression) || !setters.has(e.expression.text) || e.arguments.length !== 1) fail(sf, e, "event handler performs an effect other than a useState update or route navigation");
    const stateName = setters.get(e.expression.text);
    const arg = strip(e.arguments[0]);
    let update;
    if (ts.isArrowFunction(arg) || ts.isFunctionExpression(arg)) {
      if (arg.parameters.length !== 1 || !ts.isIdentifier(arg.parameters[0].name) || !ts.isExpression(arg.body)) fail(sf, arg, "functional state update must be a single expression");
      update = ["functional", arg.parameters[0].name.text, enc(arg.body, new Set([arg.parameters[0].name.text]))];
    } else update = ["value", enc(arg, localVars)];
    return ["set", stateName, update, lineOf(sf, e)];
  };

  const effects = pendingEffects.map(({ call, line }) => {
    if (call.arguments.length !== 2) fail(sf, call, "source effect needs an explicit dependency array");
    const callback = strip(call.arguments[0]);
    const dependencies = strip(call.arguments[1]);
    if ((!ts.isArrowFunction(callback) && !ts.isFunctionExpression(callback)) || !ts.isArrayLiteralExpression(dependencies)) fail(sf, call, "source effect needs a function and literal dependency array");
    if (dependencies.elements.some((item) => ts.isSpreadElement(item))) fail(sf, dependencies, "effect dependency spreads are outside the source model");
    if (ts.isBlock(callback.body) && callback.body.statements.some((item) => ts.isReturnStatement(item))) fail(sf, callback.body, "effect cleanup functions need lifecycle modeling");
    const body = ts.isBlock(callback.body) ? statement(callback.body) : statement(ts.factory.createExpressionStatement(callback.body));
    const deps = dependencies.elements.map((item) => enc(item, new Set()));
    return { id: `${statePrefix}effect@${path}:${line}`, owner: statePrefix || null, deps, setup: body, path, line, cleanup: null };
  });

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
  const childEffects = [];
  let componentInstance = 0;
  let renderedStatefulChildren = 0;
  const render = (e, conditionalMount = false) => {
    e = strip(e);
    if (e.kind === ts.SyntaxKind.NullKeyword || e.kind === ts.SyntaxKind.FalseKeyword) return { type: "empty" };
    if (ts.isJsxElement(e) && ts.isIdentifier(e.openingElement.tagName) && routerComponents.get(e.openingElement.tagName.text) === "Routes") return renderRoutes(e, conditionalMount);
    if (ts.isJsxElement(e) && ts.isPropertyAccessExpression(e.openingElement.tagName) && e.openingElement.tagName.name.text === "Provider") return contextProviderElement(e.openingElement, e.children, e, conditionalMount);
    if (ts.isJsxSelfClosingElement(e) && ts.isPropertyAccessExpression(e.tagName) && e.tagName.name.text === "Provider") return contextProviderElement(e, [], e, conditionalMount);
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

  function renderRoutes(e, conditionalMount) {
    const routesName = e.openingElement.tagName.text;
    if (routerComponents.get(routesName) !== "Routes" || shadows.has(routesName)) fail(sf, e.openingElement.tagName, "Routes must resolve to the runtime react-router-dom export in the mounted component");
    routerUses.add("Routes");
    const routes = [];
    for (const child of e.children) {
      if (!ts.isJsxSelfClosingElement(child) && !ts.isJsxElement(child)) continue;
      const open = ts.isJsxSelfClosingElement(child) ? child : child.openingElement;
      if (!ts.isIdentifier(open.tagName) || routerComponents.get(open.tagName.text) !== "Route" || shadows.has(open.tagName.text)) fail(sf, child, "Route must resolve to the runtime react-router-dom export");
      let routePath = null, routeElement = null;
      for (const attr of open.attributes.properties) {
        if (!ts.isJsxAttribute(attr) || !ts.isIdentifier(attr.name)) fail(sf, attr, "Route attributes must use explicit path and element expressions");
        if (attr.name.text === "path" && ts.isStringLiteralLike(attr.initializer)) routePath = attr.initializer.text;
        else if (attr.name.text === "path" && ts.isJsxExpression(attr.initializer) && attr.initializer.expression && ts.isStringLiteralLike(strip(attr.initializer.expression))) routePath = strip(attr.initializer.expression).text;
        else if (attr.name.text === "element" && ts.isJsxExpression(attr.initializer) && attr.initializer.expression) routeElement = render(attr.initializer.expression, conditionalMount);
        else if (attr.name.text !== "path" && attr.name.text !== "element") fail(sf, attr, `Route attribute '${attr.name.text}' is outside the route model`);
        else fail(sf, attr, "Route attributes must use a literal path and explicit element expression");
      }
      if (routePath === null || routeElement === null) fail(sf, child, "Route needs a literal path and element");
      if (routePath !== "*" && !routePath.startsWith("/")) fail(sf, child, "route paths must be absolute");
      routes.push({ path: routePath, render: routeElement, sourcePath: path, line: lineOf(sf, child) });
    }
    return { type: "routes", routes };
  }

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
    let componentKey = null;
    for (const a of open.attributes.properties) {
      if (!ts.isJsxAttribute(a) || !ts.isIdentifier(a.name)) fail(sf, a, "composed component spreads and namespaced props are outside the source UI model");
      const name = a.name.text;
      if (name === "key") {
        if (ts.isStringLiteral(a.initializer)) componentKey = ["lit", a.initializer.text];
        else if (ts.isJsxExpression(a.initializer) && a.initializer.expression) componentKey = enc(a.initializer.expression, new Set());
        else fail(sf, a, "component key must be a string or scalar expression");
        continue;
      }
      if (!a.initializer) { values.set(name, ["lit", true]); continue; }
      if (ts.isStringLiteral(a.initializer)) { values.set(name, ["jsx-lit", a.initializer.text]); continue; }
      if (!ts.isJsxExpression(a.initializer) || !a.initializer.expression) fail(sf, a, `composed component prop '${name}' is outside the source UI model`);
      if (/^on[A-Z]/.test(name)) handlers.set(name, handler(a.initializer.expression));
      else values.set(name, enc(a.initializer.expression, new Set()));
    }
    const instancePrefix = `${statePrefix}${target.path}@${componentInstance++}/`;
    const childContexts = new Map(activeContexts);
    for (const item of providerContextValues(target, instancePrefix, values)) childContexts.set(item.context, item.fields);
    const previousContexts = activeContexts;
    activeContexts = childContexts;
    const childStateStart = childStates.length;
    let childTree;
    try { childTree = { type: "group", children: jsxChildren(children, conditionalMount) }; }
    finally { activeContexts = previousContexts; }
    childTree.stateful = childStates.length > childStateStart;
    const nested = scanComponent(target.path, target.text, target.sf, target.node, true, { values, handlers, children: childTree, contexts: childContexts }, instancePrefix, conditionalMount);
    if (nested.states.length && values.has("key")) fail(sf, whole, `stateful child component '${open.tagName.text}' uses a React key whose identity changes are outside the source UI model`);
    childStates.push(...nested.states);
    childEffects.push(...nested.effects);
    return { type: "component", id: instancePrefix, key: componentKey, line: lineOf(sf, whole), componentPath: target.path, stateful: nested.states.length > 0, child: nested.render };
  }

  function contextProviderElement(open, children, whole, conditionalMount) {
    if (!ts.isPropertyAccessExpression(open.tagName) || open.tagName.name.text !== "Provider" || !ts.isIdentifier(open.tagName.expression)) fail(sf, open.tagName, "context provider must resolve through an imported createContext value");
    const context = contextSymbol(path, sf, open.tagName.expression.text);
    if (!context) fail(sf, open.tagName, "context provider does not resolve to this module's runtime createContext symbol");
    const attributes = open.attributes.properties;
    if (attributes.length !== 1 || !ts.isJsxAttribute(attributes[0]) || attributes[0].name.getText(sf) !== "value" || !ts.isJsxExpression(attributes[0].initializer) || !attributes[0].initializer.expression || !ts.isObjectLiteralExpression(strip(attributes[0].initializer.expression))) fail(sf, open, "context provider value must be an explicit record of state fields");
    const fields = {};
    for (const property of strip(attributes[0].initializer.expression).properties) {
      const fieldName = ts.isPropertyAssignment(property) && ts.isIdentifier(property.name) ? property.name.text
        : ts.isShorthandPropertyAssignment(property) ? property.name.text : null;
      const fieldValue = ts.isPropertyAssignment(property) ? strip(property.initializer)
        : ts.isShorthandPropertyAssignment(property) ? property.name : null;
      if (!fieldName || !fieldValue) fail(sf, property, "context provider fields must use explicit names");
      if (ts.isIdentifier(fieldValue) && setters.has(fieldValue.text)) fields[fieldName] = ["setter", setters.get(fieldValue.text)];
      else fields[fieldName] = enc(fieldValue, new Set());
    }
    return { type: "provider", context, value: fields, path, line: lineOf(sf, whole), children: jsxChildren(children, conditionalMount) };
  }

  function element(open, children, whole, conditionalMount) {
    const tag = open.tagName.getText(sf);
    if (!/^[a-z][a-z0-9-]*$/.test(tag)) fail(sf, open.tagName, `composed component '${tag}' is not yet modeled`);
    if (["a", "input", "textarea", "select", "form", "fieldset", "details", "summary", "dialog", "style", "script", "link"].includes(tag)) fail(sf, open.tagName, `native ${tag} behavior is outside the source UI model`);
    if (!modeledTags.has(tag)) fail(sf, open.tagName, `native ${tag} accessibility semantics are outside the source UI model`);
    const props = {};
    const events = {};
    let key = null;
    for (const a of open.attributes.properties) {
      if (!ts.isJsxAttribute(a)) fail(sf, a, "spread JSX attributes are outside the source UI model");
      const name = a.name.getText(sf);
      if (name === "key") {
        if (ts.isStringLiteral(a.initializer)) key = ["lit", a.initializer.text];
        else if (ts.isJsxExpression(a.initializer) && a.initializer.expression) key = enc(a.initializer.expression, new Set());
        else fail(sf, a, "native key must be a string or scalar expression");
        continue;
      }
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
    return { type: "element", tag, path, line: lineOf(sf, whole), key, props, events, children: jsxChildren(children, conditionalMount) };
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
  const effectCalls = new Set(pendingEffects.map(({ call }) => call));
  const renderTree = renderFlow(body.statements.filter((s) => !(ts.isVariableStatement(s) || ts.isFunctionDeclaration(s)) && !(ts.isExpressionStatement(s) && effectCalls.has(strip(s.expression)))), false, dynamicMount);
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
  return { path, component: component.name ? component.name.text : "default", line: lineOf(sf, component), states: [...states.values(), ...childStates], effects: [...effects, ...childEffects], render: renderTree, routerRequired: routerUses.size > 0 };
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

function reactBindings(sf, importedName) {
  const names = new Set();
  for (const statement of sf.statements) {
    if (!ts.isImportDeclaration(statement) || statement.moduleSpecifier.text !== "react") continue;
    const clause = statement.importClause;
    if (!clause || clause.isTypeOnly) continue;
    if (clause.name) names.add(clause.name.text);
    if (clause.namedBindings && ts.isNamespaceImport(clause.namedBindings)) names.add(clause.namedBindings.name.text);
    if (clause.namedBindings && ts.isNamedImports(clause.namedBindings)) {
      for (const item of clause.namedBindings.elements) {
        if (!item.isTypeOnly && (item.propertyName || item.name).text === importedName) names.add(item.name.text);
      }
    }
  }
  return names;
}

function contextSymbol(path, sf, name) {
  const createNames = reactBindings(sf, "createContext");
  for (const statement of sf.statements) {
    if (!ts.isVariableStatement(statement)) continue;
    for (const declaration of statement.declarationList.declarations) {
      if (!ts.isIdentifier(declaration.name) || declaration.name.text !== name || !declaration.initializer) continue;
      const init = strip(declaration.initializer);
      if (ts.isCallExpression(init) && ts.isIdentifier(init.expression) && createNames.has(init.expression.text)) return `${path}#${name}`;
      if (ts.isCallExpression(init) && ts.isPropertyAccessExpression(init.expression) && init.expression.name.text === "createContext" && ts.isIdentifier(init.expression.expression) && createNames.has(init.expression.expression.text)) return `${path}#${name}`;
    }
  }
  return null;
}

function providerContextValues(target, statePrefix, props = new Map()) {
  const sf = target.sf;
  const useStateNames = reactBindings(sf, "useState");
  const stateAliases = new Map();
  const isUseState = (call) => ts.isIdentifier(call.expression) && useStateNames.has(call.expression.text)
    || ts.isPropertyAccessExpression(call.expression) && call.expression.name.text === "useState" && ts.isIdentifier(call.expression.expression) && useStateNames.has(call.expression.expression.text);
  for (const statement of target.node.body.statements) {
    if (!ts.isVariableStatement(statement)) continue;
    for (const declaration of statement.declarationList.declarations) {
      const init = declaration.initializer && strip(declaration.initializer);
      if (!ts.isArrayBindingPattern(declaration.name) || !init || !ts.isCallExpression(init) || !isUseState(init)) continue;
      let initial = literal(init.arguments[0], sf);
      if (!initial && ts.isIdentifier(strip(init.arguments[0]))) {
        const value = props.get(strip(init.arguments[0]).text);
        if (value && ["lit", "jsx-lit"].includes(value[0]) && ["string", "number", "boolean"].includes(typeof value[1])) initial = ["lit", value[1]];
      }
      if (!initial) continue;
      const [value, setter] = declaration.name.elements;
      if (!value || !ts.isIdentifier(value.name) || !setter || !ts.isIdentifier(setter.name)) continue;
      const name = `${statePrefix}${value.name.text}`;
      stateAliases.set(value.name.text, ["state", name]);
      stateAliases.set(setter.name.text, ["setter", name]);
    }
  }
  const found = [];
  const visit = (node) => {
    const open = ts.isJsxElement(node) ? node.openingElement : ts.isJsxSelfClosingElement(node) ? node : null;
    if (open && ts.isPropertyAccessExpression(open.tagName) && open.tagName.name.text === "Provider" && ts.isIdentifier(open.tagName.expression)) {
      const context = contextSymbol(target.path, sf, open.tagName.expression.text);
      const attr = open.attributes.properties.find((item) => ts.isJsxAttribute(item) && item.name.getText(sf) === "value");
      if (context && attr && attr.initializer && ts.isJsxExpression(attr.initializer) && attr.initializer.expression && ts.isObjectLiteralExpression(strip(attr.initializer.expression))) {
        const fields = {};
        for (const property of strip(attr.initializer.expression).properties) {
          const fieldName = ts.isPropertyAssignment(property) && ts.isIdentifier(property.name) ? property.name.text
            : ts.isShorthandPropertyAssignment(property) ? property.name.text : null;
          const fieldValue = ts.isPropertyAssignment(property) ? strip(property.initializer)
            : ts.isShorthandPropertyAssignment(property) ? property.name : null;
          if (!fieldName || !ts.isIdentifier(fieldValue)) return;
          const value = stateAliases.get(fieldValue.text);
          if (!value) return;
          fields[fieldName] = value;
        }
        found.push({ context, fields });
      }
    }
    ts.forEachChild(node, visit);
  };
  visit(target.node.body);
  return found;
}

function contextHook(path, exportName, seen = new Set()) {
  const key = `${path}\0${exportName}`;
  if (seen.has(key)) return null;
  seen.add(key);
  const file = files.get(path);
  if (!file) return null;
  const kind = /\.(tsx|jsx)$/.test(path) ? ts.ScriptKind.TSX : /\.(jsx|js|mjs|cjs)$/.test(path) ? ts.ScriptKind.JSX : ts.ScriptKind.TS;
  const sf = ts.createSourceFile(path, file.text, ts.ScriptTarget.Latest, true, kind);
  const useContextNames = reactBindings(sf, "useContext");
  const functions = [];
  const add = (node, name, exported) => { if (name === exportName && exported) functions.push(node); };
  for (const statement of sf.statements) {
    if (ts.isFunctionDeclaration(statement) && statement.name) {
      const modifiers = ts.canHaveModifiers(statement) ? ts.getModifiers(statement) || [] : [];
      add(statement, statement.name.text, modifiers.some((modifier) => modifier.kind === ts.SyntaxKind.ExportKeyword));
    }
    if (ts.isExportDeclaration(statement) && !statement.isTypeOnly) {
      if (ts.isStringLiteralLike(statement.moduleSpecifier)) {
        const resolved = resolveModule(path, statement.moduleSpecifier.text);
        if (!resolved) continue;
        if (statement.exportClause && ts.isNamedExports(statement.exportClause)) {
          for (const item of statement.exportClause.elements) if (!item.isTypeOnly && item.name.text === exportName) {
            const result = contextHook(resolved, (item.propertyName || item.name).text, seen);
            if (result) return result;
          }
        } else if (!statement.exportClause && exportName !== "default") {
          const result = contextHook(resolved, exportName, seen);
          if (result) return result;
        }
      } else if (statement.exportClause && ts.isNamedExports(statement.exportClause)) {
        for (const item of statement.exportClause.elements) if (!item.isTypeOnly && item.name.text === exportName) {
          const local = (item.propertyName || item.name).text;
          const fn = functions.find((node) => node.name?.text === local);
          if (fn) functions.push(fn);
        }
      }
    }
  }
  if (functions.length !== 1 || !useContextNames.size) return null;
  const fn = functions[0];
  let context = null;
  const visit = (node) => {
    if (ts.isCallExpression(node) && ts.isIdentifier(node.expression) && useContextNames.has(node.expression.text) && node.arguments.length === 1 && ts.isIdentifier(node.arguments[0])) {
      const symbol = contextSymbol(path, sf, node.arguments[0].text);
      if (symbol) context = symbol;
    }
    ts.forEachChild(node, visit);
  };
  visit(fn.body);
  return context ? { path, context } : null;
}

function isContextDeclaration(sf, statement) {
  if (!ts.isVariableStatement(statement)) return false;
  return statement.declarationList.declarations.some((declaration) => ts.isIdentifier(declaration.name) && contextSymbol(sf.fileName, sf, declaration.name.text));
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
    if (!ts.isExportDeclaration(statement) || statement.isTypeOnly || !ts.isStringLiteralLike(statement.moduleSpecifier)) continue;
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
    if (!ts.isExportDeclaration(statement) || statement.isTypeOnly) continue;
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
    if (isStaticDeclaration(sf, s) || isContextDeclaration(sf, s) || ts.isVariableStatement(s) && s.declarationList.declarations.every((d) => d.initializer && (ts.isArrowFunction(strip(d.initializer)) || ts.isFunctionExpression(strip(d.initializer))))) continue;
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
  const sameTarget = (resolved) => resolved && resolved.path === target.path
    && resolved.node.getStart(resolved.sf) === target.node.getStart(target.sf);
  const rootLookup = (e) => {
    e = strip(e);
    if (!ts.isCallExpression(e) || !ts.isPropertyAccessExpression(e.expression) || !ts.isIdentifier(e.expression.expression) || e.expression.expression.text !== "document" || e.arguments.length !== 1 || !ts.isStringLiteralLike(e.arguments[0])) return false;
    if (e.expression.name.text === "getElementById") return e.arguments[0].text.length > 0 ? e.arguments[0].text : false;
    const match = e.expression.name.text === "querySelector" && e.arguments[0].text.match(/^#([A-Za-z_][\w-]*)$/);
    return match ? match[1] : false;
  };
  const jsxTag = (e) => ts.isJsxSelfClosingElement(e) ? e.tagName : ts.isJsxElement(e) ? e.openingElement.tagName : null;
  for (const f of files) {
    const kind = /\.(tsx|jsx)$/.test(f.path) ? ts.ScriptKind.TSX : /\.(jsx|js|mjs|cjs)$/.test(f.path) ? ts.ScriptKind.JSX : ts.ScriptKind.TS;
    const sf = ts.createSourceFile(f.path, f.text, ts.ScriptTarget.Latest, true, kind);
    const roots = new Set();
    const reactDomObjects = new Set();
    const targetBindings = new Set();
    const routerBindings = new Map();
    const reactNamespaces = new Set();
    const sourceComponents = new Map();
    let importsAllowed = true;
    for (const s of sf.statements) {
      if (!ts.isImportDeclaration(s) || !ts.isStringLiteralLike(s.moduleSpecifier)) continue;
      const from = s.moduleSpecifier.text;
      const clause = s.importClause;
      if (from === "react-dom/client" && clause) {
        if (!clause.isTypeOnly && clause.name) reactDomObjects.add(clause.name.text);
        if (!clause.isTypeOnly && clause.namedBindings && ts.isNamespaceImport(clause.namedBindings)) reactDomObjects.add(clause.namedBindings.name.text);
        if (!clause.isTypeOnly && clause.namedBindings && ts.isNamedImports(clause.namedBindings)) {
          for (const item of clause.namedBindings.elements) if (!item.isTypeOnly && (item.propertyName || item.name).text === "createRoot") roots.add(item.name.text);
        }
        continue;
      }
      if (from === "react" && clause) {
        if (clause.name && !clause.isTypeOnly) reactNamespaces.add(clause.name.text);
        if (clause.namedBindings && ts.isNamespaceImport(clause.namedBindings) && !clause.isTypeOnly) reactNamespaces.add(clause.namedBindings.name.text);
        continue;
      }
      if (from === "react-router-dom" && clause?.namedBindings && ts.isNamedImports(clause.namedBindings)) {
        for (const item of clause.namedBindings.elements) if (!clause.isTypeOnly && !item.isTypeOnly && (item.propertyName || item.name).text === "BrowserRouter") routerBindings.set(item.name.text, "BrowserRouter");
        continue;
      }
      if (from.startsWith(".")) {
        const importedPath = resolveModule(f.path, from);
        if (from.endsWith(".css") && importedPath && !clause) continue;
        if (!importedPath || !clause) { importsAllowed = false; continue; }
        if (clause.name && !clause.isTypeOnly) {
          const resolved = resolveNamedExport(importedPath, "default");
          if (sameTarget(resolved)) targetBindings.add(clause.name.text);
          else if (resolved) sourceComponents.set(clause.name.text, { path: resolved.path, name: resolved.name });
          else importsAllowed = false;
        }
        if (clause.namedBindings && ts.isNamedImports(clause.namedBindings)) for (const item of clause.namedBindings.elements) {
          if (clause.isTypeOnly || item.isTypeOnly) continue;
          const exportedName = (item.propertyName || item.name).text;
          const resolved = resolveNamedExport(importedPath, exportedName);
          if (sameTarget(resolved)) targetBindings.add(item.name.text);
          else if (resolved) sourceComponents.set(item.name.text, { path: resolved.path, name: resolved.name });
          else importsAllowed = false;
        }
        continue;
      }
      importsAllowed = false;
    }
    if (!importsAllowed || !targetBindings.size || (!roots.size && !reactDomObjects.size)) continue;
    const executable = sf.statements.filter((s) => !ts.isImportDeclaration(s) && !(ts.isExpressionStatement(s) && ts.isStringLiteral(s.expression)));
    if (executable.length !== 1 || !ts.isExpressionStatement(executable[0])) continue;
    const mount = strip(executable[0].expression);
    if (!ts.isCallExpression(mount) || !ts.isPropertyAccessExpression(mount.expression) || mount.expression.name.text !== "render" || mount.arguments.length !== 1) continue;
    const create = strip(mount.expression.expression);
    if (!ts.isCallExpression(create) || create.arguments.length !== 1) continue;
    const createRootCall = ts.isIdentifier(create.expression) && roots.has(create.expression.text)
      || ts.isPropertyAccessExpression(create.expression) && create.expression.name.text === "createRoot" && ts.isIdentifier(create.expression.expression) && reactDomObjects.has(create.expression.expression.text);
    if (!createRootCall) continue;
    const root = rootLookup(create.arguments[0]);
    if (!root) continue;
    const wrapperChain = [];
    let routerContext = false;
    let targetCount = 0;
    let invalidMount = false;
    let mountedTarget = null;
    const inspect = (node, parentSite = null) => {
      node = strip(node);
      if (ts.isJsxFragment(node)) {
        for (const child of node.children) {
          if (ts.isJsxText(child) && !child.text.trim()) continue;
          if (ts.isJsxExpression(child) && child.expression) { inspect(child.expression, parentSite); continue; }
          if (ts.isJsxElement(child) || ts.isJsxSelfClosingElement(child) || ts.isJsxFragment(child)) { inspect(child, parentSite); continue; }
          invalidMount = true;
        }
        return;
      }
      if (!ts.isJsxElement(node) && !ts.isJsxSelfClosingElement(node)) { invalidMount = true; return; }
      const tag = jsxTag(node);
      const props = ts.isJsxSelfClosingElement(node) ? node.attributes.properties : node.openingElement.attributes.properties;
      const children = ts.isJsxElement(node) ? node.children : [];
      if (ts.isIdentifier(tag) && targetBindings.has(tag.text)) {
        if (props.length || children.length) invalidMount = true;
        mountedTarget = { path: target.path, symbol: target.name, site: `${f.path}#mount-target-${targetCount + 1}`, parentSite, line: lineOf(sf, node) };
        targetCount++;
        return;
      }
      const site = `${f.path}#mount-${wrapperChain.length + 1}`;
      if (ts.isIdentifier(tag) && routerBindings.get(tag.text) === "BrowserRouter") {
        if (props.length) invalidMount = true;
        routerContext = true;
        wrapperChain.push({ kind: "router", name: "BrowserRouter", site, parentSite, line: lineOf(sf, node) });
      } else if (ts.isPropertyAccessExpression(tag) && ts.isIdentifier(tag.expression) && reactNamespaces.has(tag.expression.text) && tag.name.text === "StrictMode") {
        if (props.length) invalidMount = true;
        wrapperChain.push({ kind: "strict-mode", name: "React.StrictMode", site, parentSite, line: lineOf(sf, node) });
      } else if (ts.isIdentifier(tag) && sourceComponents.has(tag.text)) {
        const component = sourceComponents.get(tag.text);
        wrapperChain.push({ kind: "source-component", name: tag.text, path: component.path, symbol: component.name, site, parentSite, line: lineOf(sf, node) });
      } else { invalidMount = true; return; }
      for (const child of children) {
        if (ts.isJsxText(child) && !child.text.trim()) continue;
        if (ts.isJsxExpression(child) && child.expression) { inspect(child.expression, site); continue; }
        if (ts.isJsxElement(child) || ts.isJsxSelfClosingElement(child) || ts.isJsxFragment(child)) { inspect(child, site); continue; }
        invalidMount = true;
      }
    };
    inspect(mount.arguments[0]);
    if (!invalidMount && targetCount === 1) return { root, entry: f.path, routerContext, wrapperChain, mountedTarget };
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
    let mountRoot;
    try { mountRoot = mountedComponent({ path: f.path, name: c.name, defaultExport, sf: c.sf, node: c.node }, input.files); }
    catch (e) { errors.push(String(e && e.message || e).split("\n")[0]); continue; }
    if (!mountRoot) continue;
    connected = true;
    try {
      models.push({
        ...scanComponent(f.path, f.text, c.sf, c.node),
        mountRoot: mountRoot.root,
        mountEntry: mountRoot.entry,
        mountRouterContext: mountRoot.routerContext,
        mountWrappers: mountRoot.wrapperChain,
        mountTarget: mountRoot.mountedTarget,
      });
    }
    catch (e) {
      const reason = String(e && e.message || e).split("\n")[0];
      models.push({
        path: f.path,
        component: c.name,
        line: lineOf(c.sf, c.node),
        states: [],
        render: { type: "opaque-component", path: f.path, line: lineOf(c.sf, c.node), reason },
        sourceOpen: reason,
        mountRoot: mountRoot.root,
        mountEntry: mountRoot.entry,
        mountRouterContext: mountRoot.routerContext,
        mountWrappers: mountRoot.wrapperChain,
        mountTarget: mountRoot.mountedTarget,
      });
    }
  }
}
if (!connected) errors.push("no exported JSX component is connected to a verified React createRoot(...).render(...) entry");
process.stdout.write(JSON.stringify({ models, errors }));
