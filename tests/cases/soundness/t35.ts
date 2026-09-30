// An object escapes with the exception: whoever catches it still holds the
// object, so a throw must leave its invariant intact, like a return.
export class Acct {
  //@ invariant this.lo <= this.hi
  lo = 0;
  hi = 0;

  risky(x: number): void {
    //@ raises x < 0
    this.lo = this.hi + 1;
    if (x < 0) throw new Error("negative");
    this.hi = this.lo;
  }
}

export function spoil(accts: Acct[], x: number): void {
  //@ raises x < 0 && accts.length > 0
  if (accts.length > 0) {
    accts[0].lo = accts[0].hi + 1;
    if (x < 0) throw new Error("negative");
    accts[0].hi = accts[0].lo;
  }
}

export class Checked {
  //@ invariant this.n >= 0
  n: number;

  constructor(n: number) {
    if (n < 0) throw new Error("negative");
    this.n = n;
  }
}
