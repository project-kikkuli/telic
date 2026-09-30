// A subclass invariant over an inherited field: code typed as the base may
// break it, then a call through the base runs the override that assumed it.
export class Base {
  constructor(public x: number) {}

  setx(v: number): void {
    this.x = v;
  }

  helper(): number {
    //@ ensures result <= 100
    return Math.min(this.x, 100);
  }
}

export class Sub extends Base {
  //@ invariant this.x <= 100
  constructor(x: number) {
    //@ requires x <= 100
    super(x);
  }

  helper(): number {
    return this.x;
  }
}

export function throughBase(b: Base): number {
  //@ ensures result <= 100
  b.setx(1000);
  return b.helper();
}
