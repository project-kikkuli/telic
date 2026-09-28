export function isIntHint(p: number): number {
  //@ requires !Number.isInteger(p)
  //@ ensures result === 0
  return p - Math.floor(p);
}

