// Gradual TypeScript: none of these may prove (helpers aside).
import * as lib from "some-lib";

export class Box {
  v: number;
  constructor(v: number) {
    //@ ensures this.v === v
    this.v = v;
  }
}

export function aliasWrite(a: Box, b: Box): number {
  //@ ensures result === 1
  a.v = 1;
  b.v = 2;
  return a.v;
}

export function callbackReassigns(): number {
  //@ ensures result === 0
  let x = 0;
  lib.run(() => {
    x = 5;
  });
  return x;
}

export function storedCallback(): number {
  //@ ensures result === 0
  let x = 0;
  const bump = () => {
    x = x + 1;
  };
  lib.register(bump);
  lib.tick();
  return x;
}

export function localCall(): number {
  //@ ensures result === 0
  let x = 0;
  function bump(): void {
    x = 7;
  }
  bump();
  return x;
}

export function opaqueNull(v: any): number {
  //@ ensures result === 0
  if (v === null) return 1;
  return 0;
}

export function mapBang(m: Map<string, number>): number {
  //@ ensures result >= 0
  return m.get("k")!;
}

export function asCast(v: unknown): number {
  //@ ensures result === 1
  return v as number;
}

export async function racy(b: Box): Promise<number> {
  //@ requires b.v === 1
  //@ ensures result === 1
  await lib.sleep(1);
  return b.v;
}

export function catchPath(n: number): number {
  //@ ensures result === 1
  let y = 1;
  try {
    y = lib.compute(n);
    y = 1;
  } catch (e) {
    // swallow
  }
  return y;
}

export function chained(b: Box | undefined): number {
  //@ ensures result === 1
  return b?.v ?? 1;
}

export function filteredLen(xs: number[]): number[] {
  //@ ensures result.length === xs.length
  return xs.filter((x) => x > 0);
}
