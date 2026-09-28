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

