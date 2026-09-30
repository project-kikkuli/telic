// A subclass TypeScript lowering does not model may override what a call through its base runs.
export class Shape {
  area(): number {
    //@ ensures result >= 0
    return 0;
  }
}

export class Square extends Shape {
  area(): number {
    return -1;
  }
}

export function total(s: Shape): number {
  //@ ensures result >= 0
  return s.area();
}
