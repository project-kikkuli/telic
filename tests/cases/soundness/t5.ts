type int = number;

function zeroLast(ys: int[]): void {
  //@ requires ys.length >= 1
  //@ ensures ys.length === old(ys.length)
  //@ ensures ys[ys.length - 1] === 0
  ys[ys.length - 1] = 0;
}

export function ofMutated(xs: int[]): int {
  //@ requires xs.length === 2 && xs[0] === 5 && xs[1] === 5
  //@ ensures result === 5
  let last = 0;
  //@ index k
  //@ invariant k === 0 || last === 5
  for (const x of xs) {
    zeroLast(xs);
    last = x;
  }
  return last;
}

