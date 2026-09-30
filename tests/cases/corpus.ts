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

// expect: proved
// (no contract: throwing is what it does, e.g. an HTTP handler rejecting a request)
export function throwsAlways(x: number): number {
  if (x > 3) throw new Error("too big");
  return x;
}

// expect: refuted
export function throwsUndeclared(x: number): number {
  //@ ensures result <= 3
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

// expect: proved
export function pushAll(a: number[], b: number[]): number {
  //@ ensures result == a.length + b.length
  const out: number[] = a.slice();
  out.push(...b);
  return out.length;
}

// expect: proved
export function mapKeepsLength(xs: string[]): number {
  //@ ensures result == xs.length
  const ys = xs.map((s) => {
    console.log(s);
    return s.toUpperCase();
  });
  return ys.length;
}

// expect: refuted
export function unshiftLength(): number {
  //@ ensures result == 2
  const ys: number[] = [5];
  ys.unshift(1);
  return ys.length + ys[0] - ys[1];
}

interface Holder {
  items: number[];
  label: string;
}

// expect: proved
// (destructured props, as React components take them)
export function labelLength({ label }: Holder): number {
  return label.length;
}

type Payment = { method: "card"; last4: string; amount: number } | { method: "cash"; amount: number } | { method: "credit"; amount: number; expires?: number };

// expect: proved
export function fee(p: Payment): number {
  //@ requires p.amount >= 0
  //@ ensures result >= 0
  switch (p.method) {
    case "card":
      return p.amount / 50 + p.last4.length * 0;
    case "cash":
      return 0;
    default:
      return (p.expires ?? 1) > 0 ? p.amount : 0;
  }
}

// expect: refuted
export function feeBad(p: Payment): number {
  //@ ensures result >= 0
  if (p.method !== "card") return 0;
  return p.amount / 50;
}

// expect: proved
export function isCard(p: Payment): boolean {
  //@ ensures result === (p.method === "card")
  return p.method === "card" && p.last4.length >= 0;
}

// expect: proved
export function cash(amount: number): Payment {
  //@ ensures result.method === "cash" && result.amount === amount
  return { method: "cash", amount };
}

interface Profile {
  nick?: string;
  age?: number;
}

// expect: proved
export function greeting(p: Profile | undefined): string {
  //@ ensures result.length >= 2
  return "hi" + (p?.nick ?? "");
}

// expect: refuted
export function ageNext(p: Profile | undefined): number {
  //@ ensures result > 0
  return (p?.age ?? 0) + 1;
}

// expect: proved
export function firstOf(xs: readonly number[]): number {
  //@ requires xs.length > 0
  //@ ensures result === xs[0]
  return xs[0];
}

// expect: proved
export function lookup(m: ReadonlyMap<string, number>, k: string): number {
  //@ ensures implies(!m.has(k), result === -1)
  return m.get(k) ?? -1;
}

// expect: proved
export async function doubledLater(x: number): Promise<number> {
  //@ ensures result === 2 * x
  await Promise.resolve();
  return 2 * x;
}

interface Named {
  name: string;
}

interface Aged extends Named {
  age: number;
}

type Pet = Cat | Dog;

interface Cat extends Named {
  species: "cat";
  lives: number;
}

interface Dog extends Named {
  species: "dog";
  good: boolean;
}

// expect: proved
export function describeAged(a: Aged): number {
  //@ ensures result === a.name.length + a.age
  return a.name.length + a.age;
}

// expect: proved
export function livesLeft(p: Pet): number {
  //@ ensures result >= 0
  if (p.species === "dog") return p.good ? 1 : 0;
  return Math.max(p.lives, 0) + p.name.length * 0;
}

export class Wallet {
  //@ invariant this.cents >= 0
  cents = 0;
}

// expect: proved
export function fillWallets(ws: Wallet[], c: number): void {
  //@ requires c >= 0
  for (const w of ws) {
    if (w.cents < c) {
      w.cents = c;
    }
  }
}

// expect: proved
export function newWallets(ws: Wallet[], out: Wallet[]): void {
  for (let i = 0; i < ws.length; i++) {
    const w = new Wallet();
    w.cents = 5;
    out.push(w);
  }
}

export type Nested = { n: number; inner: { m: number; tag?: string } };

// expect: proved
export function nestedField(r: Nested): number {
  //@ ensures result === r.n + r.inner.m
  return r.n + r.inner.m;
}

// expect: refuted
export function nestedWrong(r: Nested): number {
  //@ ensures result === r.inner.m
  return r.n;
}

// expect: refuted
export function emptyWallets(ws: Wallet[]): void {
  for (const w of ws) {
    w.cents = -1;
  }
}

export class Span {
  //@ invariant this.lo <= this.hi
  lo = 0;
  hi = 0;
}

// expect: refuted
export function stretch(s: Span, x: number): void {
  //@ raises x < 0
  s.lo = s.hi + 1;
  if (x < 0) throw new Error("negative");
  s.hi = s.lo;
}

// expect: proved
export function bumpWallets(ws: Wallet[]): void {
  for (const w of ws) {
    w.cents = w.cents + 1;
  }
}

// expect: proved
export function totalCents(ws: Wallet[]): number {
  //@ ensures result >= 0
  let t = 0;
  for (const w of ws) {
    t += w.cents;
  }
  return t;
}

enum Stage { Draft, Review, Published, Archived }

export class Post {
  //@ lifecycle stage: Stage.Draft -> Stage.Review -> Stage.Published -> Stage.Archived, Stage.Review -> Stage.Draft
  //@ lifecycle never stage: Stage.Published -> Stage.Draft
  //@ lifecycle monotonic this.edits
  stage: Stage;
  edits: number;
  constructor() {
    this.stage = Stage.Draft;
    this.edits = 0;
  }
}

// expect: proved
export function publish(p: Post): void {
  if (p.stage === Stage.Review) p.stage = Stage.Published;
}

// expect: proved
export function edit(p: Post): void {
  if (p.stage === Stage.Draft || p.stage === Stage.Review) {
    p.edits = p.edits + 1;
    p.stage = Stage.Draft;
  }
}

// expect: refuted
export function unpublish(p: Post): void {
  // a published post goes back to draft: the harness checks every object parameter
  if (p.stage === Stage.Published) p.stage = Stage.Draft;
}

// Array-method callbacks: each element's obligations, under a filter's test.
function posNum(x: number): number {
  //@ requires x > 0
  //@ ensures result === x
  return x;
}

// expect: proved
export function findGuarded(xs: number[]): number {
  //@ ensures result === 0
  const y = xs.find((x) => x > 0 && posNum(x) > 1);
  return 0;
}

// expect: refuted
export function findUnguarded(xs: number[]): number {
  //@ requires xs.length <= 3
  //@ ensures result === 0
  const y = xs.find((x) => posNum(x) > 1);
  return 0;
}

// expect: proved
export function filterByIndex(xs: number[]): number {
  //@ ensures result === 0
  const y = xs.filter((x, i) => posNum(i + 1) > 1);
  return 0;
}

// expect: proved
export function mapStatementsGuarded(xs: number[]): number {
  //@ ensures result === 0
  const ys = xs.filter((x) => {
    if (x <= 0) return false;
    return posNum(x) > 2;
  });
  return 0;
}

// expect: refuted
export function mapStatementsUnguarded(xs: number[]): number {
  //@ ensures result === 0
  const ys = xs.map((x) => {
    const y = x - 1;
    return posNum(y);
  });
  return 0;
}

// expect: proved
export function parseDigits(s: string): number {
  //@ requires s === "42"
  //@ ensures result === 42
  return Number.parseInt(s, 10)
}

// expect: proved
export function parseLeadingDigit(s: string): number {
  //@ requires s.startsWith("7")
  //@ ensures result >= 0
  return parseInt(s)
}

// expect: refuted
export function parseFloatWrong(s: string): number {
  //@ requires s === "5"
  //@ ensures result === 6
  return parseFloat(s)
}
