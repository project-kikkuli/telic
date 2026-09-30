// Discriminated unions: a field only some variants have is undefined in the
// others, so it may only be read where the tag has been checked.
export type Shape = { kind: "sq"; side: number } | { kind: "dot" };

export function unguarded(s: Shape): number {
  //@ ensures result === result
  return s.side;
}

export function rebound(s: Shape, t: Shape): number {
  //@ ensures result >= 0
  let u = s;
  if (u.kind === "sq") {
    u = t;
    return u.side * u.side;
  }
  return 0;
}

export function wrongBranch(s: Shape): number {
  //@ ensures result >= 0
  if (s.kind === "sq") return 0;
  return s.side * s.side;
}

export function missingCase(s: Shape): number {
  //@ ensures result >= 0
  switch (s.kind) {
    case "sq":
      return s.side * s.side;
  }
}

export function lying(): number {
  //@ ensures result === 1
  const d: Shape = { kind: "dot", side: 1 };
  return d.kind === "dot" ? 1 : d.side;
}

// `??` replaces only undefined and null; `||` replaces every falsy value.
export function nullish(x: number | undefined): number {
  //@ requires x === 0
  //@ ensures result === 5
  return x ?? 5;
}

export function orZero(x: number | undefined): number {
  //@ requires x === 0
  //@ ensures result === 0
  return x || 5;
}
