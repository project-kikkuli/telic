// A checked class used as a value can be subclassed where telic does not
// look: a class expression, a mixin.
export class A {
  f(): number {
    //@ ensures result >= 0
    return 1;
  }
}

export const K = class extends A {
  f(): number {
    return -1;
  }
};

export function mix<T extends new (...a: any[]) => A>(Base: T) {
  return class extends Base {
    f(): number {
      return -2;
    }
  };
}

export const M = mix(A);

export function viaA(a: A): number {
  //@ ensures result >= 0
  return a.f();
}
