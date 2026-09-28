export function shadow(c: boolean): number {
  //@ ensures result === 2
  let x = 1;
  if (c) {
    let x = 2;
  }
  x = x + 0;
  if (!c) {
    let x = 2;
  }
  return x;
}

export function loopShadow(): number {
  //@ ensures result === 2
  let i = 100;
  for (let i = 0; i < 3; i++) {
  }
  return i;
}

export function isIntHint(p: number): number {
  //@ requires !Number.isInteger(p)
  //@ ensures result === 0
  return p - Math.floor(p);
}

export function isIntHint2(p: number): number {
  //@ requires Number.isInteger(p) || p > 0
  //@ ensures result === 0
  return p - Math.floor(p);
}

export function parenAlias(xs: number[]): number {
  //@ requires xs.length === 1 && xs[0] === 0
  //@ ensures result === 0
  const ys = (xs);
  ys[0] = 5;
  return xs[0];
}

function zero(ys: number[]): void {
  //@ requires ys.length >= 1
  //@ ensures ys.length === old(ys.length)
  //@ ensures ys[0] === 0
  ys[0] = 0;
}

export function hiMutated(xs: number[]): number {
  //@ requires xs.length === 1 && Number.isInteger(xs[0]) && xs[0] === 5
  //@ ensures result === 5
  let n = 0;
  //@ invariant n === i
  for (let i = 0; i < xs[0]; i++) {
    zero(xs);
    n++;
  }
  return n;
}
