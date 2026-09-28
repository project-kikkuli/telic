export function shadow(c: boolean): number {
  //@ ensures result === 2
  let x = 1;
  if (c) {
    let x = 2;
  }
  x = x + 0;
  if (!c) {
    let x = 2;
  }
  return x;
}

