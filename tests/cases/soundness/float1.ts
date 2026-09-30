// number is an IEEE double; integer-valued numbers are exact only up to 2^53.

//@ ensures result
export function classic(): boolean {
  return 0.1 + 0.2 === 0.3;
}

//@ ensures result === x
export function reflexive(x: number): number {
  return x;
}

//@ requires Number.isInteger(n)
//@ ensures result > n
export function inc(n: number): number {
  return n + 1;
}

//@ requires Number.isInteger(n) && n >= 0
//@ ensures result === n
export function backAndForth(n: number): number {
  return n + 1 - 1;
}

//@ requires Number.isInteger(n) && n === 0
//@ ensures result === Infinity
export function negZero(n: number): number {
  return 1 / (-n * 1.5);
}

//@ ensures result === 1
export function unsafe(): number {
  const big = 9007199254740992;
  return big + 1 - big;
}

//@ requires Number.isFinite(x)
//@ ensures result >= x
export function floorUp(x: number): number {
  return Math.floor(x);
}

//@ ensures Number.isInteger(result)
export function floorNaN(x: number): number {
  return Math.floor(x);
}

//@ requires Number.isInteger(price) && price >= 0 && price < 1000000
//@ ensures result === price * 3 / 100
export function tax(price: number): number {
  return (price * 0.03);
}

//@ requires Number.isInteger(a) && Number.isInteger(b) && Math.abs(a) < 1000000 && Math.abs(b) < 1000000
//@ ensures result === b + a
export function fine(a: number, b: number): number {
  return a + b;
}
