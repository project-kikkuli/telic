export function total(xs: number[]): number {
  //@ mirrors a.py::total
  let s = 0;
  for (const x of xs) s += x;
  return s;
}

export function add3(a: number, b: number, c: number): number {
  //@ mirrors a.py::add3
  return (a + b) + c;
}
