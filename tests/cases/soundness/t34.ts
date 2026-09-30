// A class invariant that reads another object's fields breaks when code that
// never touches the object writes that other one; other tasks assume it
// whenever they resume.
export class Acct {
  bal = 0;
}

export function nonneg(a: Acct | undefined): boolean {
  return a === undefined || a.bal >= 0;
}

export class Link {
  //@ invariant nonneg(this.nxt)
  nxt: Acct | undefined = undefined;
}

export class Pool {
  //@ invariant this.accts.every((self) => self.bal >= 0)
  accts: Acct[] = [];
}

export async function dip(a: Acct): Promise<void> {
  a.bal = -1;
  await new Promise((r) => setTimeout(r, 10));
  a.bal = 0;
}

export async function sees(k: Link): Promise<number> {
  //@ ensures result >= 0
  await Promise.resolve();
  if (k.nxt !== undefined) return k.nxt.bal;
  return 0;
}

export async function seesPool(p: Pool): Promise<number> {
  //@ ensures result >= 0
  await Promise.resolve();
  if (p.accts.length > 0) return p.accts[0].bal;
  return 0;
}
