// An object written inside a loop must satisfy its class invariant on return.
export class Acct {
  //@ invariant this.bal >= 0
  bal = 0;
}

export function drain(accts: Acct[]): void {
  for (const a of accts) {
    a.bal = -1;
  }
}

export function drainIdx(accts: Acct[]): void {
  for (let i = 0; i < accts.length; i++) {
    accts[i].bal = -1;
  }
}

export function drainNested(accts: Acct[]): void {
  for (const a of accts) {
    for (let j = 0; j < accts.length; j++) {
      a.bal = a.bal - 1;
    }
  }
}

export function drainAlias(accts: Acct[]): void {
  for (const a of accts) {
    const b = a;
    b.bal = -1;
  }
}

export function drainSome(accts: Acct[], cut: number): void {
  for (const a of accts) {
    if (a.bal > cut) {
      a.bal = cut;
    }
  }
}

export function refill(accts: Acct[]): void {
  for (const a of accts) {
    a.bal = 5;
  }
}
