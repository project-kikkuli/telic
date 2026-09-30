// Recursion telic cannot see as a call: through a rebound name, an arrow
// function behind a higher-order wrapper, .call, .bind, a function passed as
// an argument. Each claim throws RangeError.

function rebound(n: number): number {
  return again(n + 1);
}
const again = rebound;

export function claimRebound(n: number): number {
  //@ ensures result == 42
  rebound(n);
  return 42;
}

function wrap(f: (n: number) => number): (n: number) => number {
  return (n: number) => f(n);
}

const spin: (n: number) => number = wrap((n: number) => spin(n + 1));

export function claimWrapped(n: number): number {
  //@ ensures result == 42
  spin(n);
  return 42;
}

function viaCall(n: number): number {
  return viaCall.call(null, n + 1);
}

export function claimCall(n: number): number {
  //@ ensures result == 42
  viaCall(n);
  return 42;
}

function viaBind(n: number): number {
  const g = viaBind.bind(null);
  return g(n + 1);
}

export function claimBind(n: number): number {
  //@ ensures result == 42
  viaBind(n);
  return 42;
}

function apply(f: (n: number) => number, n: number): number {
  return f(n);
}

function passed(n: number): number {
  return apply(passed, n + 1);
}

export function claimPassed(n: number): number {
  //@ ensures result == 42
  passed(n);
  return 42;
}
