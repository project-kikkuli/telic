export function varLoop(): number {
  //@ ensures result === 2
  for (var i = 0; i < 3; i++) {
  }
  return i;
}

export function orVal(a: number, b: number): boolean {
  //@ requires a === 3
  //@ ensures result === true
  return a || b;
}

function setz(ys: number[]): number {
  //@ requires ys.length >= 1
  //@ ensures ys.length === old(ys.length)
  //@ ensures ys[0] === 0
  //@ ensures result === 0
  ys[0] = 0;
  return 0;
}

function first(a: number[], k: number): number {
  //@ requires a.length >= 1
  //@ ensures result === a[0] + k
  return a[0] + k;
}

export function staleArg(xs: number[]): number {
  //@ requires xs.length >= 1 && xs[0] === 7
  //@ ensures result === 7
  return first(xs, setz(xs));
}

export function mathRound(x: number): number {
  //@ ensures result === Math.floor(x + 0.5)
  return Math.round(x);
}
