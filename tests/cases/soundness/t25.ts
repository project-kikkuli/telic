// Vacuity: preconditions that can never hold make every claim trivially true.

export function contradictory(x: number): number {
  //@ requires x > 0 && x < 0
  //@ ensures result == 42
  return x;
}

export function fine(x: number): number {
  //@ requires x > 0
  //@ ensures result > 0
  return x;
}
