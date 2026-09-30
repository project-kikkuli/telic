// Classes that extend checked classes: inherited fields and invariants,
// overrides checked against the contract of the method they override,
// super calls, abstract classes and dispatch through a base.

export class Account {
  //@ invariant this.balance >= 0
  balance: number;

  constructor(public owner: string, balance: number) {
    //@ requires balance >= 0
    //@ ensures this.balance === balance
    this.balance = balance;
  }

  deposit(amount: number): void {
    //@ requires amount > 0
    //@ ensures this.balance === old(this.balance) + amount
    this.balance += amount;
  }

  withdraw(amount: number): number {
    //@ requires 0 < amount
    //@ ensures result <= amount
    //@ ensures this.balance === old(this.balance) - result
    const taken = Math.min(amount, this.balance);
    this.balance -= taken;
    return taken;
  }
}

export class Savings extends Account {
  //@ invariant this.rate >= 0
  rate: number;

  constructor(owner: string, balance: number, rate: number) {
    //@ requires balance >= 0 && rate >= 0
    super(owner, balance);
    this.rate = rate;
  }

  addInterest(): void {
    //@ ensures this.balance >= old(this.balance)
    this.balance += (this.balance * this.rate) / 100;
  }
}

// no constructor: it takes Account's parameters and precondition
export class Capped extends Account {
  limit = 100;

  // no contract: inherits Account.withdraw's, and is checked against it
  withdraw(amount: number): number {
    const taken = Math.min(amount, this.balance, this.limit);
    this.balance -= taken;
    return taken;
  }
}

export class Leaky extends Account {
  // breaks the inherited '@ensures result <= amount'
  withdraw(amount: number): number {
    return amount + 1;
  }
}

export class Logged extends Account {
  count = 0;

  deposit(amount: number): void {
    this.count += 1;
    super.deposit(amount);
  }
}

export function savingsDeposit(s: Savings): number {
  //@ ensures result > old(s.balance)
  s.deposit(5); // inherited: runs Account.deposit on a Savings
  return s.balance;
}

export function throughBase(a: Account): number {
  //@ ensures result <= 10
  return a.withdraw(10); // may run Capped.withdraw or Leaky.withdraw
}

export function openCapped(): number {
  //@ ensures result === 7
  const c = new Capped("ann", 7);
  return c.balance;
}

export function badSavings(): Savings {
  return new Savings("bo", -1, 2);
}

export abstract class Shape {
  //@ ensures result >= 0
  abstract area(): number;

  twice(): number {
    //@ ensures result >= 0
    return 2 * this.area();
  }
}

export class Square extends Shape {
  constructor(public side: number) {
    super();
  }

  area(): number {
    return this.side * this.side;
  }
}

export class Hole extends Shape {
  area(): number {
    return -1;
  }
}

export function totalArea(s: Shape, t: Shape): number {
  //@ ensures result >= 0
  return s.area() + t.area();
}

// the guard for a call without 'new', which a class constructor never gets
export class Guarded {
  v: number;

  constructor(v: number) {
    //@ ensures this.v === v
    if (!(this instanceof Guarded)) {
      return new Guarded(v);
    }
    this.v = v;
  }
}
