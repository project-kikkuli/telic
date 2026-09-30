// An untyped parameter that looks read-only but lets its argument be changed:
// through a nested value, a value flowing through ?? or ?:, a return, a
// pass-on to a writer, a method call.
export type In = { kind: "sq" | "dot" };
export type Out = { inner: In; n: number };

function setKind(o: any): void {
  o.kind = "dot";
}

function nested(o: unknown): void {
  setKind((o as any).inner);
}

function orElse(o: unknown): void {
  const p: any = o ?? {};
  p.n = 5;
}

function pick(c: boolean, o: unknown): void {
  (c ? o : ({} as any)).n = 5;
}

function same(o: unknown): unknown {
  return o;
}

function push(o: any): void {
  if (o.length === 1) o.push(2);
}

function via(o: unknown): void {
  setKind(o);
}

export function viaNested(x: Out): number {
  //@ ensures result === 1
  if (x.inner.kind !== "sq") return 1;
  nested(x);
  return x.inner.kind === "sq" ? 1 : 0;
}

export function viaOrElse(x: Out): number {
  //@ ensures result === 0
  if (x.n !== 0) return 0;
  orElse(x);
  return x.n;
}

export function viaPick(x: Out): number {
  //@ ensures result === 0
  if (x.n !== 0) return 0;
  pick(true, x);
  return x.n;
}

export function viaReturn(x: Out): number {
  //@ ensures result === 0
  if (x.n !== 0) return 0;
  const y: any = same(x);
  y.n = 5;
  return x.n;
}

export function viaPush(xs: number[]): number {
  //@ requires xs.length === 1
  //@ ensures result === 1
  push(xs);
  return xs.length;
}

export function viaPassOn(x: In): number {
  //@ ensures result === 1
  if (x.kind !== "sq") return 1;
  via(x);
  return x.kind === "sq" ? 1 : 0;
}
