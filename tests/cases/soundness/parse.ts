export function nanIsNotAnInteger(s: string): boolean {
  // parseInt of text with no digits is NaN, not an integer
  //@ ensures result
  return Number.isInteger(parseInt(s))
}

export function prefixOnly(s: string): number {
  // parseInt reads only the leading digits: parseInt("12px") === 12
  //@ requires s === "12px"
  //@ ensures result !== 12
  return parseInt(s)
}
