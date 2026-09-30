// A call to an async function that is not awaited returns at its first await.
export class Counter {
  n = 0;
}

export async function bump(c: Counter): Promise<void> {
  //@ ensures c.n === old(c.n) + 1
  const k = c.n;
  await Promise.resolve();
  c.n = k + 1;
}

export function kick(c: Counter): number {
  //@ ensures result === old(c.n) + 1
  bump(c);
  return c.n;
}

export function set(c: Counter): void {
  //@ ensures c.n === 5
  c.n = 5;
}

// `void f()` still runs f.
export function discarded(c: Counter): number {
  //@ ensures result === 1
  c.n = 1;
  void set(c);
  return c.n;
}
