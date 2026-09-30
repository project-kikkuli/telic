// Array-method callbacks (the TypeScript comprehensions): every element's
// obligations and effects must survive. Every function below except the
// helpers must NOT prove.

function pos(x: number): number {
  //@ requires x > 0
  //@ ensures result === x
  return x;
}

function boom(x: number): number {
  //@ ensures result === x
  if (x === 3) throw new Error("three");
  return x;
}

class Counter {
  n: number;
  constructor() {
    //@ ensures this.n === 0
    this.n = 0;
  }
  bump(): number {
    //@ ensures this.n === old(this.n) + 1
    //@ ensures result === 0
    this.n = this.n + 1;
    return 0;
  }
}

export function preInMap(xs: number[]): number[] {
  //@ ensures result.length === xs.length
  return xs.map((x) => pos(x));
}

export function raiseInMap(xs: number[]): number[] {
  //@ ensures result.length === xs.length
  return xs.map((x) => boom(x));
}

export function effectInMap(c: Counter, xs: number[]): number {
  //@ requires c.n === 0
  //@ ensures result === 0
  const ys = xs.map((x) => c.bump());
  return c.n;
}

export function preInFind(xs: number[]): number {
  //@ ensures result === 0
  const y = xs.find((x) => pos(x) > 1);
  return 0;
}

export function preInFilterIndex(xs: number[]): number {
  //@ ensures result === 0
  const y = xs.filter((x, i) => pos(i) > 1);
  return 0;
}

export function preInMapBlock(xs: number[]): number {
  //@ ensures result === 0
  const y = xs.map((x) => { const z = pos(x); return z + 1; });
  return 0;
}

export function preInSort(xs: number[]): number {
  //@ ensures result === 0
  const y = [...xs].sort((a, b) => pos(a) - b);
  return 0;
}

export function preInForEach(xs: number[]): number {
  //@ ensures result === 0
  xs.forEach((x) => pos(x));
  return 0;
}

export function effectInSome(c: Counter, xs: number[]): number {
  //@ requires c.n === 0
  //@ ensures result === 0
  const b = xs.some((x) => c.bump() > 0);
  return c.n;
}

export function preInFunctionRef(xs: number[]): number {
  //@ ensures result === 0
  const y = xs.map(pos);
  return 0;
}

export function preInFlatMap(xs: number[]): number {
  //@ ensures result === 0
  const y = xs.flatMap((x) => [pos(x)]);
  return 0;
}

export function effectInFindIndex(c: Counter, xs: number[]): number {
  //@ requires c.n === 0
  //@ ensures result === 0
  const i = xs.findIndex((x) => c.bump() > x);
  return c.n;
}

export function preInMapStatements(xs: number[]): number {
  //@ ensures result === 0
  const ys = xs.map((x) => {
    const y = x - 1;
    return pos(y);
  });
  return 0;
}

export function countsInMapStatements(xs: number[]): number {
  //@ ensures result === 0
  let n = 0;
  const ys = xs.map((x) => {
    n = n + 1;
    return x;
  });
  return n;
}

export function preInForEachReturn(xs: number[]): number {
  //@ ensures result === 0
  xs.forEach((x) => {
    return pos(x);
  });
  return 0;
}
