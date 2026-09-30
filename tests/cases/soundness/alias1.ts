// Records and arrays are values to telic but objects to JavaScript: an
// untyped alias of one (a cast, an untyped parameter) writes the original.
export type Shape = { kind: "sq"; side: number } | { kind: "dot" };

function flip(o: { kind: string }): void {
  o.kind = "dot";
}

export function mutated(s: Shape): number {
  //@ ensures result === 1
  if (s.kind === "sq") {
    flip(s);
    return s.kind === "sq" ? 1 : 0;
  }
  return 1;
}

export function cast(s: Shape): number {
  //@ ensures result === 1
  if (s.kind === "sq") {
    (s as any).kind = "dot";
    return s.kind === "sq" ? 1 : 0;
  }
  return 1;
}

export function aliasVar(s: Shape): number {
  //@ ensures result === 1
  if (s.kind === "sq") {
    const o: any = s;
    o.kind = "dot";
    return s.kind === "sq" ? 1 : 0;
  }
  return 1;
}

function grow(o: any): void {
  o.push(5);
}

export function grown(xs: number[]): number {
  //@ ensures result === old(xs.length)
  grow(xs);
  return xs.length;
}

export function castPush(xs: number[]): number {
  //@ ensures result === old(xs.length)
  (xs as any).push(5);
  return xs.length;
}

export class Holder {
  o: any = null;
}

export function stored(s: Shape, h: Holder): number {
  //@ ensures result === 1
  if (s.kind === "sq") {
    h.o = s;
    h.o.kind = "dot";
    return s.kind === "sq" ? 1 : 0;
  }
  return 1;
}
