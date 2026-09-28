function zero(ys: number[]): void {
  //@ requires ys.length >= 1
  //@ ensures ys.length === old(ys.length)
  //@ ensures ys[0] === 0
  ys[0] = 0;
}

