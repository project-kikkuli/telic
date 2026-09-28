type int = number;

function zero(ys: int[]): void {
  //@ requires ys.length >= 1
  //@ ensures ys.length === old(ys.length)
  //@ ensures ys[0] === 0
  ys[0] = 0;
}

export function hiMutated(xs: int[]): int {
  //@ requires xs.length === 1 && xs[0] === 5
  //@ ensures result === 5
  let n = 0;
  //@ invariant n === i
  for (let i = 0; i < xs[0]; i++) {
    zero(xs);
    n++;
  }
  return n;
}

export function ofMutated(xs: int[]): int {
  //@ requires xs.length === 2 && xs[0] === 5 && xs[1] === 5
  //@ ensures result === 5
  let last = 0;
  //@ index k
  //@ invariant k === 0 || last === 5
  for (const x of xs) {
    zero(xs);
    last = x;
  }
  return last;
}

export function localIntReal(): int {
  //@ ensures result === 0
  const x: int = 0.5;
  return Math.floor(x) * 2 - 1;
}
