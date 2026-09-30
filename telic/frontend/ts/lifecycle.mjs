// Lifecycle lines: parsing and the host-syntax texts to lower (mirrors telic/lifecycle.py).

const GRAPH_RE = /^(?:(?:self|this)\.)?([A-Za-z_]\w*)\s*:(?!:)\s*([\s\S]+)$/;

export class LifecycleError extends Error {}

function split(text, sep) {
  const out = [];
  let depth = 0, quote = "", cur = "";
  for (let i = 0; i < text.length; i++) {
    const ch = text[i];
    if (quote) {
      cur += ch;
      if (ch === "\\" && i + 1 < text.length) cur += text[++i];
      else if (ch === quote) quote = "";
    } else if ("\"'`".includes(ch)) {
      quote = ch;
      cur += ch;
    } else if ("([{".includes(ch)) {
      depth++;
      cur += ch;
    } else if (")]}".includes(ch)) {
      depth--;
      cur += ch;
    } else if (depth === 0 && text.startsWith(sep, i) && !(sep === "|" && text.startsWith("||", i))) {
      out.push(cur);
      cur = "";
      i += sep.length - 1;
    } else cur += ch;
  }
  out.push(cur);
  return out.map((x) => x.split(/\s+/).filter(Boolean).join(" "));
}

function edgesOf(body) {
  const edges = [];
  for (const chain of split(body, ",")) {
    if (!chain) continue;
    const stops = split(chain, "->").map((stop) => split(stop, "|"));
    if (stops.length < 2 || stops.some((stop) => stop.some((s) => !s))) throw new LifecycleError(`'${chain}' is not a transition: write 'A -> B' (chains 'A -> B -> C' and alternatives 'A | B -> C' work too)`);
    for (let k = 0; k + 1 < stops.length; k++)
      for (const a of stops[k]) for (const b of stops[k + 1]) if (!edges.some(([x, y]) => x === a && y === b)) edges.push([a, b]);
  }
  if (!edges.length) throw new LifecycleError("no transitions listed");
  return edges;
}

export function parseLifecycle(payload) {
  const text = payload.split(/\s+/).filter(Boolean).join(" ");
  if (!text) throw new LifecycleError("empty '@lifecycle'");
  const sp = text.indexOf(" ");
  const word = sp < 0 ? text : text.slice(0, sp), rest = sp < 0 ? "" : text.slice(sp + 1);
  if (word === "never") {
    const m = GRAPH_RE.exec(rest);
    if (!m) throw new LifecycleError("write 'never FIELD: A -> B'");
    return { kind: "never", field: m[1], edges: edgesOf(m[2]), expr: "" };
  }
  if (word === "monotonic" || word === "once") {
    if (!rest) throw new LifecycleError(`'${word}' needs an expression over the object's fields`);
    return { kind: word, field: "", edges: [], expr: rest };
  }
  const m = GRAPH_RE.exec(text);
  if (m && m[2].includes("->")) return { kind: "graph", field: m[1], edges: edgesOf(m[2]), expr: "" };
  if (!text.includes("old(")) throw new LifecycleError("a lifecycle relates an object before a call (old(...)) to after it; or write 'FIELD: A -> B', 'never FIELD: A -> B', 'monotonic E' or 'once P'");
  return { kind: "step", field: "", edges: [], expr: text };
}

function closure(edges) {
  const states = [];
  for (const [a, b] of edges) for (const s of [a, b]) if (!states.includes(s)) states.push(s);
  const out = [];
  for (const s of states) {
    const seen = [];
    const todo = edges.filter(([a]) => a === s).map(([, b]) => b);
    while (todo.length) {
      const t = todo.shift();
      if (seen.includes(t)) continue;
      seen.push(t);
      todo.push(...edges.filter(([a]) => a === t).map(([, b]) => b));
    }
    for (const t of seen) if (t !== s) out.push([s, t]);
  }
  return out;
}

// { relation, probes: [[label, step, created|null]] } in TypeScript syntax.
export function lifecycleTexts(form) {
  const par = (x) => `(${x})`;
  if (form.kind === "graph" || form.kind === "never") {
    const s = `this.${form.field}`;
    const eq = (a, b) => `${a} === ${b}`;
    const pair = (a, b) => par(`${eq(`old(${s})`, a)} && ${eq(s, b)}`);
    if (form.kind === "graph") {
      const rel = [eq(`old(${s})`, s), ...closure(form.edges).map(([a, b]) => pair(a, b))].join(" || ");
      return { relation: rel, probes: form.edges.map(([a, b]) => [`${a} -> ${b}`, pair(a, b), null]) };
    }
    const rel = form.edges.map(([a, b]) => `!${pair(a, b)}`).join(" && ");
    const probes = [];
    for (const [a] of form.edges) if (!probes.some(([l]) => l === `reaches ${a}`)) probes.push([`reaches ${a}`, par(`!${par(eq(`old(${s})`, a))} && ${eq(s, a)}`), eq(s, a)]);
    return { relation: rel, probes };
  }
  const e = form.expr;
  if (form.kind === "monotonic") return { relation: `old(${e}) <= ${par(e)}`, probes: [["grows", `old(${e}) < ${par(e)}`, null]] };
  if (form.kind === "once") return { relation: `!${par(`old(${e})`)} || ${par(e)}`, probes: [["becomes true", `!${par(`old(${e})`)} && ${par(e)}`, e]] };
  return { relation: e, probes: [] };
}
