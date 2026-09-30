// The TypeScript side: a trusted predicate implies only its @ensures.
type int = number;

//@ trusted
//@ ensures implies(result, typeof t === "object" && t !== null && "a" in t)
function hasA(t: any): boolean {
  return typeof t === "object" && t !== null && "a" in t;
}

//@ requires hasA(t)
//@ ensures result
function hasB(t: any): boolean {
  return "b" in t;
}

//@ ensures result
function always(t: any): boolean {
  return hasA(t);
}

//@ ensures result
function literalEq(x: any): boolean {
  return x !== "a" || x === "b";
}
