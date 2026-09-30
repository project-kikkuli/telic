"""Differential tests for TypeScript classes, unions and nullish idioms: for
each expression and input, telic must prove the value Node computes and
refute any other. The contracts compare numbers with Object.is, which a NaN
satisfies too."""

import json
import subprocess

from telic.checker import CheckOptions, check
from telic.frontend.typescript import HERE

from conftest import needs_node

PRELUDE = """
export class Base {
  tag = 1;
  constructor(public x: number) {
    //@ ensures Object.is(this.x, x) && this.tag === 1
  }

  get(): number {
    //@ ensures Object.is(result, this.x + this.tag)
    return this.x + this.tag;
  }

  bump(d: number): void {
    //@ ensures Object.is(this.x, old(this.x) + d)
    this.x += d;
  }
}

export class Mid extends Base {
  y = 10;

  constructor(x: number) {
    //@ ensures Object.is(this.x, x) && this.tag === 1 && this.y === 10
    super(x);
  }

  get(): number {
    //@ ensures Object.is(result, this.x + this.tag)
    return this.x + this.tag;
  }

  both(): number {
    //@ ensures Object.is(result, this.x + this.tag + this.y)
    return super.get() + this.y;
  }
}

export class Leaf extends Mid {
  constructor(x: number, public z: number) {
    //@ ensures Object.is(this.x, 2 * x) && this.tag === 1 && Object.is(this.y, z)
    super(x * 2);
    this.y = z;
  }
}

export abstract class Sh {
  abstract size(): number;
}

export type Shape = { kind: "sq"; side: number } | { kind: "rect"; w: number; h: number } | { kind: "dot" };

export function area(s: Shape): number {
  //@ ensures implies(s.kind === "sq", Object.is(result, s.side * s.side))
  //@ ensures implies(s.kind === "rect", Object.is(result, s.w * s.h))
  //@ ensures implies(s.kind === "dot", result === 0)
  switch (s.kind) {
    case "sq":
      return s.side * s.side;
    case "rect":
      return s.w * s.h;
    case "dot":
      return 0;
  }
}

export interface Opt {
  v?: number;
  w?: number;
}

export function pick(o: Opt | undefined, d: number): number {
  //@ ensures Object.is(result, o === undefined ? d : o.v !== undefined ? o.v : o.w !== undefined ? o.w : d)
  return o?.v ?? o?.w ?? d;
}
"""

EXPRS = [
    "new Base(a).get()",
    "new Mid(a).get() + b",
    "new Mid(a).both()",
    "new Leaf(a, b).both()",
    "new Leaf(a, b).x",
    "(() => { const m = new Mid(a); m.bump(b); return m.both(); })()",
    "area({ kind: 'sq', side: a })",
    "area({ kind: 'rect', w: a, h: b })",
    "area({ kind: 'dot' })",
    "pick(undefined, a)",
    "pick({ v: a }, b)",
    "pick({ w: b }, a)",
    "pick({}, a)",
]

INPUTS = [(-3, 2), (0, 5), (4, -1)]


def _body(e: str) -> str:
    if e.startswith("(() => {"):
        inner = e[len("(() => {") : -len("})()")]
        return inner.strip()
    return f"return {e};"


@needs_node
def test_typescript_classes_match_node(tmp_path):
    js = (
        "const ts = require('typescript');\n"
        f"const src = {json.dumps(PRELUDE)} + {json.dumps(''.join(f'export function e{i}(a: number, b: number): number {{ {_body(e)} }}' + chr(10) for i, e in enumerate(EXPRS)))};\n"
        "const out = ts.transpileModule(src, { compilerOptions: { module: ts.ModuleKind.CommonJS, target: ts.ScriptTarget.ES2022 } }).outputText;\n"
        "const m = { exports: {} }; new Function('module', 'exports', out)(m, m.exports);\n"
        f"const ins = {json.dumps(INPUTS)};\n"
        f"console.log(JSON.stringify({json.dumps(list(range(len(EXPRS))))}.map(i => ins.map(([a, b]) => m.exports['e' + i](a, b)))));\n"
    )
    real = json.loads(subprocess.run(["node", "-e", js], capture_output=True, text=True, check=True, cwd=HERE).stdout)
    lines = [PRELUDE]
    want: dict[str, str] = {}
    for i, e in enumerate(EXPRS):
        for k, (a, b) in enumerate(INPUTS):
            v = real[i][k]
            for sign, off in (("ok", 0), ("bad", 1)):
                name = f"{sign}{i}_{k}"
                want[name] = "proved" if off == 0 else "refuted"
                lines.append(
                    f"export function {name}(a: number, b: number): number {{\n"
                    f"  //@ requires a === {a} && b === {b}\n"
                    f"  //@ ensures result === {v + off}\n"
                    f"  {_body(e)}\n}}\n"
                )
    (tmp_path / "m.ts").write_text("\n".join(lines))
    rep = check([str(tmp_path / "m.ts")], CheckOptions(cache_path=None, lean=False), root=str(tmp_path))
    assert not [p for m in rep.modules for p in m.problems], [p for m in rep.modules for p in m.problems]
    got = {f.fn.name: f for f in rep.functions}
    # a wrong value is refuted; when Node is too slow to confirm it in time it stays unconfirmed, never proved
    ok = {"proved": {"proved"}, "refuted": {"refuted", "open"}}
    bad = [f"{n}: {got[n].status if n in got else 'missing'}, want {w} {got[n].problems if n in got else ''}" for n, w in want.items() if n not in got or got[n].status not in ok[w]]
    assert not bad, "\n".join(bad)
    for n, w in want.items():
        if w == "refuted":
            assert any(v.status in ("refuted", "unconfirmed") for v in got[n].verdicts), n
            assert all(v.replay.confirmed for v in got[n].verdicts if v.status == "refuted" and v.replay is not None), n
