// Verification corpus (TypeScript). '// expect: STATUS' precedes each function.

interface Item {
  price: number;
  qty: number;
}

type int = number;

// expect: proved
export function absVal(x: number): number {
  //@ ensures result >= 0
  if (x < 0) return -x;
  return x;
}

// expect: refuted
export function absBad(x: number): number {
  //@ ensures result >= 0
  if (x < -1) return -x;
  return x;
}

// expect: proved
export function sumList(xs: number[]): number {
  //@ ensures result === sum(xs)
  let total = 0;
  for (const x of xs) {
    total += x;
  }
  return total;
}

// expect: proved
export function sumReduce(xs: number[]): number {
  //@ ensures result === sum(xs)
  return xs.reduce((a, b) => a + b, 0);
}

// expect: proved
export function indexOf(xs: number[], target: number): number {
  //@ ensures -1 <= result && result < xs.length
  //@ ensures implies(result >= 0, xs[result] === target)
  //@ invariant range(0, i).every(j => xs[j] !== target)
  for (let i = 0; i < xs.length; i++) {
    if (xs[i] === target) return i;
  }
  return -1;
}

// expect: proved
export function orderTotal(items: Item[]): number {
  //@ requires items.every(it => it.price >= 0 && it.qty >= 0)
  //@ ensures result >= 0
  let total = 0;
  for (const it of items) {
    total += it.price * it.qty;
  }
  return total;
}

// expect: proved
export function bsearch(xs: number[], target: number): number {
  //@ requires range(0, xs.length - 1).every(i => xs[i] <= xs[i + 1])
  //@ ensures -1 <= result && result < xs.length
  //@ ensures implies(result >= 0, xs[result] === target)
  let lo = 0;
  let hi = xs.length - 1;
  while (lo <= hi) {
    const mid = Math.floor((lo + hi) / 2);
    if (xs[mid] === target) return mid;
    if (xs[mid] < target) lo = mid + 1;
    else hi = mid - 1;
  }
  return -1;
}

// expect: refuted
export function lastBad(xs: number[]): number {
  return xs[xs.length];
}

// expect: refuted
export function meanBad(xs: number[]): number {
  return xs.reduce((a, b) => a + b, 0) / xs.length;
}

// expect: proved
export function mean(xs: number[]): number {
  //@ requires xs.length > 0
  //@ requires xs.every(x => x >= 0)
  //@ ensures result >= 0
  return xs.reduce((a, b) => a + b, 0) / xs.length;
}

// expect: proved
export function jsMod(a: number, b: number): number {
  //@ requires Number.isInteger(a) && Number.isInteger(b)
  //@ requires a >= 0 && b > 0
  //@ ensures 0 <= result && result < b
  return a % b;
}

// expect: refuted
export function jsModNeg(a: number, b: number): number {
  //@ requires Number.isInteger(a) && Number.isInteger(b) && b > 0
  //@ ensures 0 <= result
  return a % b;
}

// expect: proved
export function clamp(x: number, lo: number, hi: number): number {
  //@ requires lo <= hi
  //@ ensures lo <= result && result <= hi
  return Math.max(lo, Math.min(x, hi));
}

// expect: proved
export function useClamp(x: number): number {
  //@ ensures 0 <= result && result <= 100
  return clamp(x, 0, 100);
}

// expect: refuted
export function badCall(x: number): number {
  return clamp(x, 10, 0);
}

// expect: proved
export function fillZero(xs: number[]): void {
  //@ ensures xs.length === old(xs.length)
  //@ ensures xs.every(x => x === 0)
  //@ invariant range(0, i).every(j => xs[j] === 0)
  for (let i = 0; i < xs.length; i++) {
    xs[i] = 0;
  }
}

// expect: proved
export function evens(n: int): int[] {
  //@ requires n >= 0
  //@ ensures result.length === n
  //@ ensures result.every(x => x % 2 === 0)
  const out: int[] = [];
  //@ invariant out.every(x => x % 2 === 0)
  for (let i = 0; i < n; i++) {
    out.push(2 * i);
  }
  return out;
}

// expect: refuted
export function throwsAlways(x: number): number {
  if (x > 3) throw new Error("too big");
  return x;
}

// expect: proved
export function throwsDeclared(x: number): number {
  //@ raises x > 3
  if (x > 3) throw new Error("too big");
  return x;
}

// expect: proved
export function countdown(n: int): number {
  //@ requires n >= 0
  //@ ensures result === 0
  while (n > 0) {
    n--;
  }
  return n;
}

// expect: refuted
export function roundHalf(cents: int): number {
  //@ requires cents >= 0
  //@ ensures result * 2 <= cents
  return Math.round(cents / 2);
}

// expect: proved
export function label(paid: boolean, shipped: boolean): string {
  //@ ensures implies(shipped, result === "shipped")
  if (shipped) return "shipped";
  if (paid) return "paid";
  return "open";
}

// expect: proved
export function usesMap(x: number): number {
  //@ ensures result === x
  const m = new Map<string, number>();
  m.set("a", x);
  return m.get("a")!;
}

// expect: refuted
export function missingKey(x: number): number {
  const m = new Map<string, number>();
  m.set("a", x);
  return m.get("b")!;
}
