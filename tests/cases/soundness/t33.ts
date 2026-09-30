// A task suspended at `await` lets other tasks run, and they assume every
// object satisfies its invariant there.
export class Acct {
  //@ invariant this.bal >= 0
  bal = 0;
}

export async function dip(a: Acct): Promise<void> {
  a.bal = -1;
  await Promise.resolve();
  a.bal = 5;
}

export async function dipListed(accts: Acct[]): Promise<void> {
  if (accts.length > 0) {
    accts[0].bal = -1;
    await Promise.resolve();
    accts[0].bal = 5;
  }
}

export async function sees(a: Acct): Promise<number> {
  //@ ensures result >= 0
  await Promise.resolve();
  return a.bal;
}
