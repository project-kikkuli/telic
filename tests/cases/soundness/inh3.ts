// A subclass that redeclares an inherited field without an initializer
// resets it to undefined after the base constructor ran.
export class A {
  x = 5;
}

export class B extends A {
  x!: number;
}

export function five(): number {
  //@ ensures result === 5
  return new B().x;
}
