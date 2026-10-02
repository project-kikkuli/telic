export function zero_reciprocal_is_positive(x: number): number {
  //@ requires x == 0.0
  //@ ensures result > 0.0
  return 1.0 / x
}
