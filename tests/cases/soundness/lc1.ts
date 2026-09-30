// Lifecycles in TypeScript: transitivity, 'never' across calls, and objects
// written through an array.

export class Meter {
  // true of each call, false across two
  //@ lifecycle this.v <= old(this.v) + 1 && old(this.v) <= this.v
  v: number;
  constructor() {
    this.v = 0;
  }
  tick(): void {
    this.v = this.v + 1;
  }
}

export class Lock {
  //@ lifecycle once this.sealed
  sealed: boolean;
  constructor() {
    this.sealed = false;
  }
  seal(): void {
    this.sealed = true;
  }
}

export function breakAll(locks: Lock[]): void {
  for (const l of locks) {
    l.sealed = false;
  }
}

export class Stepper {
  //@ lifecycle stage: 0 -> 1 -> 2
  //@ lifecycle never stage: 0 -> 2
  stage: number;
  constructor() {
    this.stage = 0;
  }
  next(): void {
    if (this.stage === 0 || this.stage === 1) this.stage = this.stage + 1;
  }
}
