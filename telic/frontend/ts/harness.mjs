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

function decode(v) {
  if (Array.isArray(v)) return guard(v.map(decode));
  if (v && typeof v === "object" && "__real__" in v) return v.__real__[0] / v.__real__[1];
  if (v && typeof v === "object" && "__record__" in v) {
    const o = {};
    for (const [k, x] of Object.entries(v.fields)) o[k] = decode(x);
    return o;
  }
  return v;
}

function show(v) {
  if (v === undefined) return "undefined";
  if (typeof v === "number") return Object.is(v, -0) ? "-0" : String(v);
  if (typeof v === "string") return JSON.stringify(v);
  if (Array.isArray(v)) return "[" + Array.from({ length: v.length }, (_, i) => show(Reflect.get(v, i))).join(", ") + "]";
  if (v && typeof v === "object") return "{ " + Object.entries(v).map(([k, x]) => `${k}: ${show(x)}`).join(", ") + " }";
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

function wrap(name, fn, c) {
  if (!c || (!c.requires.length && !c.ensures.length)) return fn;
  const params = c.params;
  const reqs = c.requires.map((t) => [t, compileSpec(params, t)]);
  const ens = c.ensures.map((t) => {
    const [rewritten, olds] = extractOld(t);
    return [t, compileSpec(params, rewritten), olds.map((o) => compileSpec(params, o))];
  });
  const H = Object.values(helpers);
  return function (...args) {
    for (const [t, f] of reqs) if (!f(...args, undefined, [], ...H)) throw new Violation("requires", t, name);
    const entry = args.map((a, i) => (c.lists.includes(i) ? a : a));
    const olds = ens.map(([, , os]) => os.map((o) => structuredCloneSafe(o(...args, undefined, [], ...H))));
    const r = fn.apply(this, args);
    ens.forEach(([t, f], k) => {
      if (!f(...entry, r, olds[k], ...H)) throw new Violation("ensures", t, name, `returned ${show(r)}`);
    });
    return r;
  };
}

function structuredCloneSafe(v) {
  if (Array.isArray(v)) return v.map(structuredCloneSafe);
  if (v && typeof v === "object") return { ...v };
  return v;
}

function load(path, contracts) {
  const src = fs.readFileSync(path, "utf8");
  const sf = ts.createSourceFile(path, src, ts.ScriptTarget.Latest, true);
  const decls = [], consts = [];
  for (const st of sf.statements) {
    if (ts.isFunctionDeclaration(st) && st.name && st.body) decls.push(st.name.text);
    else if (ts.isVariableStatement(st)) for (const d of st.declarationList.declarations) if (ts.isIdentifier(d.name)) consts.push(d.name.text);
  }
  let suffix = "\n;";
  for (const n of decls) if (contracts[n]) suffix += `${n} = (globalThis as any).__telic_wrap(${JSON.stringify(n)}, ${n});\n`;
  suffix += `(globalThis as any).__telic_fns = { ${decls.concat(consts).join(", ")} };\n`;
  const js = ts.transpileModule(src + suffix, { compilerOptions: { module: ts.ModuleKind.CommonJS, target: ts.ScriptTarget.ES2022 } }).outputText;
  const sandbox = { module: { exports: {} }, exports: {}, require, console: { log() {}, error() {}, warn() {}, info() {}, debug() {} }, structuredClone };
  sandbox.globalThis = sandbox;
  sandbox.__telic_wrap = (n, f) => wrap(n, f, contracts[n]);
  vm.createContext(sandbox);
  vm.runInContext(js, sandbox, { filename: path, timeout: 4000 });
  const fns = sandbox.__telic_fns;
  // const-declared functions cannot be rebound; wrap them at the boundary
  for (const n of consts) if (contracts[n] && typeof fns[n] === "function") fns[n] = wrap(n, fns[n], contracts[n]);
  return fns;
}

function outcome(fn, args) {
  try {
    const r = fn(...args);
    return { returned_repr: show(r), nonfinite: typeof r === "number" && !Number.isFinite(r), returned_is_none: r === undefined };
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
      for (const [f, t] of ty.fields) o[f] = gen(t, r);
      return o;
    }
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

const deep = (v) => (Array.isArray(v) ? guard(v.map(deep)) : v && typeof v === "object" ? { ...v } : v);
const failed = (o, fname) => o && (o.crash || (o.violation && !(o.violation === "requires" && o.func === fname)) || o.nonfinite);
const plain = (v) => (Array.isArray(v) ? Array.from({ length: v.length }, (_, i) => plain(Reflect.get(v, i))) : v);

function fuzz(fn, types, n, fname) {
  const r = rng(0xc0ffee);
  let accepted = 0;
  for (let t = 0; t < n * 20 && accepted < n; t++) {
    let args = types.map((ty) => gen(ty, r));
    let o = outcome(fn, args.map(deep));
    if (o.violation === "requires" && o.func === fname) continue;
    accepted++;
    if (!failed(o, fname)) continue;
    const key = JSON.stringify([o.violation, o.text, o.crash, !!o.nonfinite]);
    for (let round = 0; round < 200; round++) {
      let progress = false;
      outer: for (let i = 0; i < args.length; i++) {
        for (const b of smaller(args[i])) {
          const cand = args.slice(0, i).concat([b], args.slice(i + 1));
          const o2 = outcome(fn, cand.map(deep));
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
process.stdin.on("end", () => {
  const req = JSON.parse(input);
  let fns;
  try {
    fns = load(req.path, req.contracts || {});
  } catch (e) {
    console.log(JSON.stringify({ harness_error: `${e.name}: ${e.message}` }));
    return;
  }
  const fn = fns[req.func];
  if (typeof fn !== "function") {
    console.log(JSON.stringify({ harness_error: `no function '${req.func}'` }));
    return;
  }
  if (req.fuzz) {
    console.log(JSON.stringify(fuzz(fn, req.types, req.fuzz, req.func)));
    return;
  }
  console.log(JSON.stringify(outcome(fn, (req.args || []).map(decode))));
});
