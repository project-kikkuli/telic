// Counterexamples holding objects inside maps, arrays and sets.
class Lock {
  held: boolean;
  constructor() {
    this.held = false;
  }
}

//@ requires locks.has(k) && locks.get(k)!.held
//@ ensures result
function freeAt(locks: Map<number, Lock>, k: number): boolean {
  return !locks.get(k)!.held;
}

//@ requires locks.length > 0 && locks[0].held
//@ ensures result
function firstFree(locks: Lock[]): boolean {
  return !locks[0].held;
}

//@ requires s.size > 0
//@ ensures result == 0
function count(s: Set<Lock>): number {
  return s.size;
}
