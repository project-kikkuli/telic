"""An untyped (unknown/any) parameter of a checked function may receive a
record or array telic models as a value: accepted when the function only
reads primitives through it, rejected when the value could be changed or
escape through it."""

import pytest

from telic.checker import CheckOptions, check

from conftest import needs_node

CALLER = """
export type Inner = { m: number };
export type Rec = { kind: "a" | "b"; n: number; inner: Inner };

HELPER

export function caller(r: Rec): number {
  //@ ensures Object.is(result, r.n)
  look(r);
  return r.n;
}
"""

READS = [
    "function look(x: unknown): boolean { return typeof x === 'object' && x !== null && 'n' in x; }",
    "function look(x: any): number { return x.n + x.inner.m * 2; }",
    "function look(x: any): string { return `${x.kind}:${x.n}`; }",
    "function look(x: any): void { if (x && x.n > 0) console.log(x.inner.m); }",
    "function look(x: any): number { return x.kind === 'a' ? -x.n : 0; }",
    "function look(x: unknown): string { return JSON.stringify(x); }",
    "function seen(y: unknown): boolean { return y === null; }\nfunction look(x: unknown): boolean { return seen(x); }",
]

WRITES = [
    "function look(x: any): void { x.n = 1; }",
    "function look(x: any): void { x.inner.m = 1; }",
    "function look(x: any): void { x.n++; }",
    "function look(x: any): void { delete x.n; }",
    "function look(x: any): void { x.touch(); }",
    "function look(x: any): unknown { return x; }",
    "function look(x: any): unknown { return x.inner; }",
    "function look(x: any): void { const y = x ?? {}; y.n = 1; }",
    "function look(x: any): void { const { inner } = x; inner.m = 1; }",
    "function look(x: any): void { Object.assign(x, { n: 1 }); }",
    "function look(x: any): void { [x].forEach((v) => (v.n = 1)); }",
    "function set(y: any): void { y.n = 1; }\nfunction look(x: unknown): void { set(x); }",
    "function look(x: any): void { (() => { x.n = 1; })(); }",
    "function look(x: any): void { arguments[0].n = 1; }",
]


def _caller(tmp_path, helper):
    f = tmp_path / "u.ts"
    f.write_text(CALLER.replace("HELPER", helper))
    rep = check([str(f)], CheckOptions(cache_path=None, lean=False), root=str(tmp_path))
    return next(r for r in rep.functions if r.fn.name == "caller")


@needs_node
@pytest.mark.parametrize("helper", READS)
def test_a_reader_is_accepted(tmp_path, helper):
    assert _caller(tmp_path, helper).status == "proved"


@needs_node
@pytest.mark.parametrize("helper", WRITES)
def test_a_writer_is_rejected(tmp_path, helper):
    r = _caller(tmp_path, helper)
    assert r.status == "unsupported", r.status
