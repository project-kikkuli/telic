export function parenAlias(xs: number[]): number {
  //@ requires xs.length === 1 && xs[0] === 0
  //@ ensures result === 0
  const ys = (xs);
  ys[0] = 5;
  return xs[0];
}

