type int = number;
export function size(s: string): int {
  //@ mirrors a.py::size
  return s.length;
}

export function before(s: string, t: string): boolean {
  //@ mirrors a.py::before
  return s < t;
}
