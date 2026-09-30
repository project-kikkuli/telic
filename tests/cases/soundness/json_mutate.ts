// JavaScript's view of an untyped value: objects change, == is loose, null
// is not undefined, and 'in' sees inherited properties.
type int = number;

//@ trusted
//@ ensures result === (k in x)
function hasKey(x: any, k: string): boolean {
  return k in x;
}

//@ requires typeof t === "object" && t !== null && !("x" in t)
//@ ensures !("x" in t)
function setField(t: any): void {
  t.x = 1;
}

//@ requires typeof t === "object" && t !== null && !("x" in t)
//@ ensures !("x" in t)
function throughView(t: any): void {
  const d: Record<string, any> = t;
  d["x"] = 1;
}

//@ requires t == "1"
//@ ensures result
function looseEq(t: any): boolean {
  return t === "1";
}

//@ requires t.k === undefined
//@ ensures result
function nullIsNotUndefined(t: any): boolean {
  return t.k === null;
}

//@ ensures result
function inherited(): boolean {
  const d: Record<string, any> = {};
  return !hasKey(d, "toString");
}

//@ ensures result
function mapEntries(): boolean {
  const d: Map<string, any> = new Map();
  d.set("a", 1);
  return hasKey(d, "a");
}

//@ requires typeof t === "object" && t !== null && !("x" in t)
//@ ensures !("x" in t)
function inCallback(t: any): void {
  [1].forEach(() => {
    t.x = 1;
  });
}
