function inc(ys: number[]): boolean {
  //@ requires ys.length >= 1
  //@ ensures ys.length === old(ys.length)
  //@ ensures ys[0] === old(ys[0]) + 1
  ys[0] = ys[0] + 1;
  return true;
}
export function logged(xs: number[]): number {
  //@ requires xs.length === 1 && xs[0] === 0
  //@ ensures result === 0
  console.log(inc(xs));
  return xs[0];
}
