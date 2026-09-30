// Functions handed on as values run where telic cannot see the call: array
// callbacks with statement bodies, reduce, promise callbacks, timers, event
// listeners, callbacks given to unchecked code, and a checked function used
// as a value. Each callback fails for some element or argument.

function pos(x: number): number {
  //@ requires x >= 1
  return x - 1;
}

function sortThrows(xs: number[]): number {
  //@ ensures result === 0
  xs.sort((a, b) => {
    if (a === b) throw new Error("duplicate");
    return a - b;
  });
  return 0;
}

function someNeedsPos(xs: number[]): number {
  //@ ensures result === 0
  const t = xs.some((x) => {
    const y = pos(x);
    return y > 1;
  });
  return 0;
}

function reduceThrows(xs: number[]): number {
  //@ ensures result === 0
  const t = xs.reduce((a, x) => {
    if (x < 0) throw new Error("negative");
    return a + x;
  }, 0);
  return 0;
}

function reduceNeedsPos(xs: number[]): number {
  //@ ensures result === 0
  const t = xs.reduce((a, x) => a + pos(x), 0);
  return 0;
}

function thenNeedsPos(p: Promise<number>): number {
  //@ ensures result === 0
  p.then((x) => pos(x));
  return 0;
}

function timerThrows(n: number): number {
  //@ ensures result === 0
  setTimeout(() => {
    if (n < 0) throw new Error("negative");
  }, 1);
  return 0;
}

function listenerNeedsPos(el: HTMLElement, n: number): number {
  //@ ensures result === 0
  el.addEventListener("click", () => pos(n));
  return 0;
}

function unknownCaller(f: (g: (x: number) => number) => void): number {
  //@ ensures result === 0
  f((x: number) => pos(x));
  return 0;
}

function namedAsValue(n: number): number {
  //@ ensures result === 0
  setTimeout(pos, n);
  return 0;
}
