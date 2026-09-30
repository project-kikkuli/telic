// `this.m()` in a base method runs the override; `super.m()` runs the base's.
export class A {
  m(): number {
    return 1;
  }

  n(): number {
    //@ ensures result === 1
    return this.m();
  }

  viaSuper(): number {
    return this.m();
  }
}

export class B extends A {
  m(): number {
    return 2;
  }

  k(): number {
    //@ ensures result === 2
    return super.m();
  }
}

export function one(a: A): number {
  //@ ensures result === 1
  return a.m();
}
