// The TypeScript side: rebuilt objects, and undefined is not null.

//@ requires t.k === undefined
//@ ensures result
function missingIsNull(t: any): boolean {
  return t.k === null;
}

//@ requires typeof t === "object" && t !== null && !("x" in t)
//@ ensures !("x" in t)
function setsField(t: any): void {
  t.x = 1;
}
