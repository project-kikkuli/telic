// Run one TypeScript function with its @requires/@ensures enforced.
// stdin: {"path", "func", "args", "contracts"?, "fuzz"?, "types"?}
// stdout: one JSON line describing what happened.

import { createRequire } from "node:module";
import fs from "node:fs";
import vm from "node:vm";

const require = createRequire(import.meta.url);
const ts = require("typescript");

class Violation extends Error {
  constructor(kind, text, func, detail = "") {
    super(`${func}: @${kind} ${text} failed ${detail}`);
    this.telic = { violation: kind, text, func, detail };
  }
}

const OOB = "telic-out-of-bounds";

function guard(arr) {
  return new Proxy(arr, {
    get(t, p, r) {
      if (typeof p === "string" && /^-?\d+$/.test(p)) {
        const i = Number(p);
        if (i < 0 || i >= t.length) {
          const e = new RangeError(`index ${i} is out of bounds for length ${t.length}`);
          e[OOB] = true;
          throw e;
        }
      }
      return Reflect.get(t, p, r);
    },
  });
}

// A stand-in for anything telic knows nothing about (opaque values, modules
// that are not installed): every property and call yields another stub.
function stub(name = "stub") {
  const f = function () {};
  return new Proxy(f, {
    get(t, p) {
      if (p === Symbol.toPrimitive) return () => NaN;
      if (p === "then") return undefined;
      if (p === "toString") return () => `<${name}>`;
      return stub(`${name}.${String(p)}`);
    },
    apply() {
      return stub(`${name}()`);
    },
    construct() {
      return stub(`new ${name}`);
    },
  });
}

let SCOPE = {};

// JSON from the solver's model -> JavaScript values. `ty` (when known)
// decides between a Map and a plain object; objects with the same reference
// decode to the same JavaScript object, so aliasing is reproduced.
function decode(v, ty = null, memo = new Map()) {
  if (v === null || v === undefined) return undefined;
  if (Array.isArray(v)) return guard(v.map((x) => decode(x, ty && ty.k === "list" ? ty.elem : null, memo)));
  if (typeof v !== "object") return v;
  if ("__real__" in v) return v.__real__[0] / v.__real__[1];
  if ("__opaque__" in v) return stub("opaque");
  if ("__enum__" in v) {
    const E = SCOPE[v.__enum__];
    return E ? E[v.member] : v.member;
  }
  if ("__object__" in v) {
    const key = `${v.__object__}#${v.ref}`;
    if (memo.has(key)) {
      const o = memo.get(key);
      if (v.fields) for (const [k, x] of Object.entries(v.fields)) o[k] = decode(x, null, memo);
      return o;
    }
    const C = SCOPE[v.__object__];
    const o = C && C.prototype ? Object.create(C.prototype) : {};
    memo.set(key, o);
    for (const [k, x] of Object.entries(v.fields || {})) {
      try {
        Object.defineProperty(o, k, { value: decode(x, null, memo), writable: true, enumerable: true, configurable: true });
      } catch {}
    }
    return o;
  }
  if ("__dict__" in v) {
    const asObject = ty && ty.k === "dict" && ty.js === "object";
    if (asObject) {
      const o = {};
      for (const [k, x] of v.__dict__) o[k] = decode(x, ty.val, memo);
      return o;
    }
    return new Map(v.__dict__.map(([k, x]) => [decode(k, null, memo), decode(x, ty && ty.val, memo)]));
  }
  if ("__record__" in v) {
    const o = {};
    for (const [k, x] of Object.entries(v.fields)) {
      const d = decode(x, null, memo);
      if (d !== undefined) o[k] = d;
    }
    return o;
  }
  return v;
}

function show(v, depth = 0) {
  if (v === undefined) return "undefined";
  if (v === null) return "null";
  if (typeof v === "number") return Object.is(v, -0) ? "-0" : String(v);
  if (typeof v === "string") return JSON.stringify(v);
  if (typeof v === "function") return "<function>";
  if (depth > 3) return "…";
  if (Array.isArray(v)) return "[" + Array.from({ length: v.length }, (_, i) => show(Reflect.get(v, i), depth + 1)).join(", ") + "]";
  if (v instanceof Map) return "Map { " + [...v.entries()].map(([k, x]) => `${show(k)} => ${show(x, depth + 1)}`).join(", ") + " }";
  if (v && typeof v === "object") {
    const name = v.constructor && v.constructor !== Object ? v.constructor.name + " " : "";
    return name + "{ " + Object.entries(v).map(([k, x]) => `${k}: ${show(x, depth + 1)}`).join(", ") + " }";
  }
  return String(v);
}

const helpers = {
  implies: (a, b) => !a || !!b,
  sum: (xs) => xs.reduce((a, b) => a + b, 0),
  count: (xs, v) => xs.filter((x) => x === v).length,
  range: (lo, hi) => ({
    every: (f) => {
      for (let i = lo; i < hi; i++) if (!f(i)) return false;
      return true;
    },
    some: (f) => {
      for (let i = lo; i < hi; i++) if (f(i)) return true;
      return false;
    },
  }),
};

function toJs(text) {
  return ts.transpileModule("(" + text + ")", { compilerOptions: { target: ts.ScriptTarget.ES2022 } }).outputText.trim().replace(/;$/, "");
}

// Replace old(e) by __old[k]; return [rewritten text, [e texts]].
function extractOld(text) {
  const sf = ts.createSourceFile("s.ts", text, ts.ScriptTarget.Latest, true);
  const olds = [];
  const cuts = [];
  const visit = (n) => {
    if (ts.isCallExpression(n) && ts.isIdentifier(n.expression) && n.expression.text === "old" && n.arguments.length === 1) {
      cuts.push([n.getStart(sf), n.getEnd(), n.arguments[0].getText(sf)]);
      return;
    }
    ts.forEachChild(n, visit);
  };
  visit(sf);
  cuts.sort((a, b) => a[0] - b[0]);
  let out = "", last = 0;
  cuts.forEach(([s, e, inner], k) => {
    out += text.slice(last, s) + `__old[${k}]`;
    olds.push(inner);
    last = e;
  });
  out += text.slice(last);
  return [out, olds];
}

function compileSpec(params, text) {
  const js = toJs(text);
  return new Function(...params, "result", "__old", ...Object.keys(helpers), `return (${js});`);
}

// Enforce a function's (or method's) @requires/@ensures. For a method the
// contract's `this` is the receiver.
function wrap(name, fn, c) {
  if (!c || (!c.requires.length && !c.ensures.length)) return fn;
  const params = c.params[0] === "self" ? c.params.slice(1) : c.params;
  const reqs = c.requires.map((t) => [t, compileSpec(params, t)]);
  const ens = c.ensures.map((t) => {
    const [rewritten, olds] = extractOld(t);
    return [t, compileSpec(params, rewritten), olds.map((o) => compileSpec(params, o))];
  });
  const H = Object.values(helpers);
  return function (...args) {
    for (const [t, f] of reqs) if (!f.call(this, ...args, undefined, [], ...H)) throw new Violation("requires", t, name);
    const olds = ens.map(([, , os]) => os.map((o) => structuredCloneSafe(o.call(this, ...args, undefined, [], ...H))));
    const self = this;
    const r = fn.apply(this, args);
    const done = (v) => {
      ens.forEach(([t, f], k) => {
        if (!f.call(self, ...args, v, olds[k], ...H)) throw new Violation("ensures", t, name, `returned ${show(v)}`);
      });
      return v;
    };
    return r && typeof r.then === "function" ? r.then(done) : done(r);
  };
}

// A constructor's contract: @requires on its arguments before it runs,
// @ensures of the object it built.
function wrapClass(name, C, c) {
  if (!c || (!c.requires.length && !c.ensures.length) || typeof C !== "function") return C;
  const params = c.params.slice(1);
  const reqs = c.requires.map((t) => [t, compileSpec(params, t)]);
  const ens = c.ensures.map((t) => [t, compileSpec(params, extractOld(t)[0])]);
  const H = Object.values(helpers);
  return new Proxy(C, {
    construct(target, args, newTarget) {
      for (const [t, f] of reqs) if (!f.call(undefined, ...args, undefined, [], ...H)) throw new Violation("requires", t, name);
      const o = Reflect.construct(target, args, newTarget === C ? target : newTarget);
      for (const [t, f] of ens) if (!f.call(o, ...args, undefined, [], ...H)) throw new Violation("ensures", t, name, `built ${show(o)}`);
      return o;
    },
  });
}

function structuredCloneSafe(v) {
  if (Array.isArray(v)) return v.map(structuredCloneSafe);
  if (v && typeof v === "object") return { ...v };
  return v;
}

// Load a module (and the checked .ts modules it imports) into one sandbox;
// packages that are not installed become stubs.
const nodePath = require("node:path");
function makeRequire(fromFile, cache, sandbox) {
  return (spec) => {
    if (spec.startsWith(".")) {
      const base = nodePath.resolve(nodePath.dirname(fromFile), spec);
      for (const cand of [base, base + ".ts", base + ".tsx", nodePath.join(base, "index.ts"), base.replace(/\.js$/, ".ts")]) {
        if (fs.existsSync(cand) && fs.statSync(cand).isFile() && /\.tsx?$/.test(cand)) return loadModule(cand, cache, sandbox).exports;
      }
    }
    try {
      return require(spec);
    } catch {
      return new Proxy({}, { get: (t, p) => (p === "__esModule" ? true : stub(`${spec}.${String(p)}`)) });
    }
  };
}

function loadModule(file, cache, sandbox) {
  if (cache.has(file)) return cache.get(file);
  const mod = { exports: {} };
  cache.set(file, mod);
  const src = fs.readFileSync(file, "utf8");
  const js = ts.transpileModule(src, { compilerOptions: { module: ts.ModuleKind.CommonJS, target: ts.ScriptTarget.ES2022, esModuleInterop: true } }).outputText;
  const fn = vm.runInContext(`(function (exports, require, module, __filename, __dirname) {${js}\n})`, sandbox, { filename: file, timeout: 4000 });
  fn(mod.exports, makeRequire(file, cache, sandbox), mod, file, nodePath.dirname(file));
  return mod;
}

function load(path, contracts) {
  const src = fs.readFileSync(path, "utf8");
  const sf = ts.createSourceFile(path, src, ts.ScriptTarget.Latest, true);
  const decls = [], consts = [], classes = [];
  for (const st of sf.statements) {
    if (ts.isFunctionDeclaration(st) && st.name && st.body) decls.push(st.name.text);
    else if (ts.isVariableStatement(st)) {
      for (const d of st.declarationList.declarations) if (ts.isIdentifier(d.name)) consts.push(d.name.text);
    } else if ((ts.isClassDeclaration(st) || ts.isEnumDeclaration(st)) && st.name) classes.push(st.name.text);
  }
  let suffix = "\n;";
  for (const n of decls) if (contracts[n]) suffix += `${n} = (globalThis as any).__telic_wrap(${JSON.stringify(n)}, ${n});\n`;
  for (const n of classes) if (contracts[`${n}.__init__`]) suffix += `${n} = (globalThis as any).__telic_wrap_class(${JSON.stringify(`${n}.__init__`)}, ${n});\n`;
  suffix += `(globalThis as any).__telic_fns = { ${decls.concat(consts, classes).join(", ")} };\n`;
  const js = ts.transpileModule(src + suffix, { compilerOptions: { module: ts.ModuleKind.CommonJS, target: ts.ScriptTarget.ES2022, esModuleInterop: true } }).outputText;
  const sandbox = { console: { log() {}, error() {}, warn() {}, info() {}, debug() {} }, structuredClone, Map, Set, Date, JSON, Math, Promise, Error, TypeError, RangeError, Number, String, Object, Array, Symbol, parseInt, parseFloat, isNaN, isFinite, setTimeout, clearTimeout };
  sandbox.globalThis = sandbox;
  sandbox.__telic_wrap = (n, f) => wrap(n, f, contracts[n]);
  sandbox.__telic_wrap_class = (n, C) => wrapClass(n, C, contracts[n]);
  vm.createContext(sandbox);
  const cache = new Map();
  const mod = { exports: {} };
  cache.set(path, mod);
  const fn = vm.runInContext(`(function (exports, require, module, __filename, __dirname) {${js}\n})`, sandbox, { filename: path, timeout: 4000 });
  fn(mod.exports, makeRequire(path, cache, sandbox), mod, path, nodePath.dirname(path));
  const fns = sandbox.__telic_fns;
  SCOPE = fns;
  // const-declared functions cannot be rebound; wrap them at the boundary
  for (const n of consts) if (contracts[n] && typeof fns[n] === "function") fns[n] = wrap(n, fns[n], contracts[n]);
  // methods: wrap on the prototype
  for (const [key, c] of Object.entries(contracts)) {
    const parts = key.split(".");
    if (parts.length < 2 || !fns[parts[0]] || !fns[parts[0]].prototype) continue;
    const C = fns[parts[0]], m = parts[1];
    if (m === "__init__" || parts.length > 2) continue;
    const desc = Object.getOwnPropertyDescriptor(C.prototype, m);
    if (desc && typeof desc.value === "function") C.prototype[m] = wrap(key, desc.value, c);
    else if (typeof C[m] === "function") C[m] = wrap(key, C[m], c);
  }
  return fns;
}

// "f", "Cls.method", "Cls.prop" (a getter), "Cls.prop.setter", "Cls.__init__".
function resolveFn(fns, name) {
  if (typeof fns[name] === "function" && !name.includes(".")) return fns[name];
  const [cls, m, extra] = name.split(".");
  const C = fns[cls];
  if (!C) return null;
  if (m === "__init__") return (self, ...args) => new C(...args);
  if (typeof C[m] === "function" && !(C.prototype && Object.getOwnPropertyDescriptor(C.prototype, m))) return (...args) => C[m](...args);
  const desc = C.prototype && Object.getOwnPropertyDescriptor(C.prototype, m);
  if (!desc) return null;
  if (extra === "setter") return (self, v) => {
    self[m] = v;
  };
  if (desc.get) return (self) => self[m];
  if (typeof desc.value === "function") return (self, ...args) => desc.value.apply(self, args);
  return null;
}

async function outcome(fn, args) {
  try {
    let r = fn(...args);
    if (r && typeof r.then === "function") r = await r;
    return { value: plain(r), returned_repr: show(r), nonfinite: typeof r === "number" && !Number.isFinite(r), returned_is_none: r === undefined };
  } catch (e) {
    if (e && e.telic) return { ...e.telic };
    if (e && e[OOB]) return { crash: "RangeError", msg: e.message, oob: true };
    if (e instanceof RangeError && /call stack/.test(e.message)) return { crash: "RangeError", msg: "maximum call stack size exceeded" };
    return { crash: (e && e.name) || "Error", msg: String((e && e.message) || e) };
  }
}

// -- fuzzing ---------------------------------------------------------------

function rng(seed) {
  let s = seed >>> 0;
  return () => {
    s = (s * 1664525 + 1013904223) >>> 0;
    return s / 4294967296;
  };
}

function gen(ty, r) {
  const pick = (xs) => xs[Math.floor(r() * xs.length)];
  switch (ty.k) {
    case "int": {
      const x = r();
      if (x < 0.5) return pick([0, 1, -1, 2, 3, 4, 5, 7, 10, -2, 100]);
      if (x < 0.85) return Math.floor(r() * 41) - 20;
      return Math.floor(r() * 2001) - 1000;
    }
    case "real":
      return r() < 0.6 ? pick([0, 0.5, 1, 1.5, 2.5, -0.5, 0.25, 3, 10, 0.1]) : Math.round((r() * 100 - 50) * 100) / 100;
    case "bool":
      return r() < 0.5;
    case "str":
      return pick(["", "a", "b", "draft", "paid", "x"]);
    case "list": {
      const n = pick([0, 1, 1, 2, 2, 3, 3, 4, 5, 6, 8]);
      return Array.from({ length: n }, () => gen(ty.elem, r));
    }
    case "record": {
      const o = {};
      for (const [f, t] of ty.fields) {
        const v = gen(t, r);
        if (v !== undefined) o[f] = v;
      }
      return o;
    }
    case "option":
      return r() < 0.25 ? undefined : gen(ty.inner, r);
    case "dict": {
      const n = pick([0, 1, 1, 2, 3]);
      const entries = Array.from({ length: n }, () => [gen(ty.key, r), gen(ty.val, r)]);
      return ty.js === "object" ? Object.fromEntries(entries) : new Map(entries);
    }
    case "enum": {
      const E = SCOPE[ty.name];
      const m = pick(ty.members);
      return E ? E[m] : m;
    }
    case "class": {
      const C = SCOPE[ty.name];
      const o = C && C.prototype ? Object.create(C.prototype) : {};
      for (const [f, t] of ty.fields || []) {
        try {
          Object.defineProperty(o, f, { value: gen(t, r), writable: true, enumerable: true, configurable: true });
        } catch {}
      }
      return o;
    }
    case "opaque":
      return stub("opaque");
  }
  return null;
}

function* smaller(v) {
  if (typeof v === "boolean") {
    if (v) yield false;
    return;
  }
  if (typeof v === "number") {
    if (v !== 0) {
      yield 0;
      yield Number.isInteger(v) ? Math.trunc(v / 2) : v / 2;
      if (Number.isInteger(v)) yield v > 0 ? v - 1 : v + 1;
      else yield Math.trunc(v);
    }
    return;
  }
  if (Array.isArray(v)) {
    for (let i = 0; i < v.length; i++) yield v.slice(0, i).concat(v.slice(i + 1));
    for (let i = 0; i < v.length; i++) for (const y of smaller(v[i])) yield v.slice(0, i).concat([y], v.slice(i + 1));
  }
}

const deep = (v) => (Array.isArray(v) ? guard(v.map(deep)) : v instanceof Map ? new Map(v) : v && typeof v === "object" && Object.getPrototypeOf(v) === Object.prototype ? { ...v } : v && typeof v === "object" && typeof v !== "function" ? Object.assign(Object.create(Object.getPrototypeOf(v)), v) : v);
const failed = (o, fname) => o && (o.crash || (o.violation && !(o.violation === "requires" && o.func === fname)) || o.nonfinite);
const plain = (v) => (Array.isArray(v) ? Array.from({ length: v.length }, (_, i) => plain(Reflect.get(v, i))) : v);

async function fuzz(fn, types, n, fname) {
  const r = rng(0xc0ffee);
  let accepted = 0;
  for (let t = 0; t < n * 20 && accepted < n; t++) {
    let args = types.map((ty) => gen(ty, r));
    let o = await outcome(fn, args.map(deep));
    if (o.violation === "requires" && o.func === fname) continue;
    accepted++;
    if (!failed(o, fname)) continue;
    const key = JSON.stringify([o.violation, o.text, o.crash, !!o.nonfinite]);
    for (let round = 0; round < 200; round++) {
      let progress = false;
      outer: for (let i = 0; i < args.length; i++) {
        for (const b of smaller(args[i])) {
          const cand = args.slice(0, i).concat([b], args.slice(i + 1));
          const o2 = await outcome(fn, cand.map(deep));
          if (failed(o2, fname) && JSON.stringify([o2.violation, o2.text, o2.crash, !!o2.nonfinite]) === key) {
            args = cand;
            o = o2;
            progress = true;
            break outer;
          }
        }
      }
      if (!progress) break;
    }
    return { found: true, args_repr: args.map((a) => show(plain(a))).join(", "), tried: accepted, ...o, violation: o.violation || (o.nonfinite ? "nonfinite" : undefined), text: o.text || (o.nonfinite ? `returned ${o.returned_repr}` : undefined) };
  }
  return { found: false, tried: accepted };
}

// ---------------------------------------------------------------------------

let input = "";
process.stdin.on("data", (d) => (input += d));
process.stdin.on("end", async () => {
  const req = JSON.parse(input);
  let fns;
  try {
    fns = load(req.path, req.contracts || {});
  } catch (e) {
    console.log(JSON.stringify({ harness_error: `${e.name}: ${e.message}` }));
    return;
  }
  const fn = resolveFn(fns, req.func);
  if (typeof fn !== "function") {
    console.log(JSON.stringify({ harness_error: `no function '${req.func}'` }));
    return;
  }
  const types = req.types || [];
  const dec = (raw) => {
    const memo = new Map();
    return raw.map((a, i) => decode(a, types[i] || null, memo));
  };
  if (req.batch) {
    const results = [];
    for (const raw of req.batch) results.push(await (async () => {
      const o = await outcome(fn, dec(raw));
      if (o.violation === "requires" && o.func === req.func) return { rejected: true };
      if (o.violation || o.crash) return { error: o.violation ? `@${o.violation} ${o.text} failed` : `${o.crash}: ${o.msg}` };
      return { ok: true, value: o.value, repr: o.returned_repr };
    })());
    console.log(JSON.stringify({ results }));
    return;
  }
  if (req.fuzz) {
    console.log(JSON.stringify(await fuzz(fn, req.types, req.fuzz, req.func)));
    return;
  }
  console.log(JSON.stringify(await outcome(fn, dec(req.args || []))));
});
