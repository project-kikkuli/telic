export function isIntHint2(p: number): number {
  //@ requires Number.isInteger(p) || p > 0
  //@ ensures result === 0
  return p - Math.floor(p);
}

