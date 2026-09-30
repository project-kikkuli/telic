// An object read out of an array is assumed to satisfy its invariant. That
// holds only if nobody the reader can't see has it broken: the reader itself,
// a caller waiting on a call, or code typed as a base class.
export class Acct {
  //@ invariant this.bal >= 0
  bal = 0;
}

export function peek(accts: Acct[]): number {
  //@ ensures result >= 0
  if (accts.length > 0) return accts[0].bal;
  return 0;
}

export function aliased(a: Acct, accts: Acct[]): number {
  //@ ensures result >= 0
  a.bal = -1;
  let r = 0;
  if (accts.length > 0) r = accts[0].bal;
  a.bal = 0;
  return r;
}

export function acrossCall(a: Acct, accts: Acct[]): number {
  //@ ensures result >= 0
  a.bal = -1;
  const r = peek(accts);
  a.bal = 0;
  return r;
}

export class Base {
  x = 0;
}

export class Capped extends Base {
  //@ invariant this.x <= 100
}

export function lift(b: Base): void {
  b.x = 1000;
}

export function cappedFirst(cs: Capped[]): number {
  //@ ensures result <= 100
  if (cs.length > 0) return cs[0].x;
  return 0;
}
