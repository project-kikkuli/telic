// A base constructor that calls a method on `this` runs the override before
// the subclass has set its fields: `n` is still undefined.
export class Base {
  //@ invariant this.z >= 0
  z: number;

  constructor() {
    this.z = 0;
    this.z = this.size();
  }

  size(): number {
    //@ ensures result >= 0
    return 0;
  }
}

export class Sub extends Base {
  //@ invariant this.n >= 0
  n: number;

  constructor(n: number) {
    //@ requires n >= 0
    super();
    this.n = n;
  }

  size(): number {
    return this.n;
  }
}

export function made(): number {
  //@ ensures result >= 0
  return new Sub(1).z;
}
