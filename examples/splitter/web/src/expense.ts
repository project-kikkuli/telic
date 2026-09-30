import type { int } from './split'

export type Status = 'draft' | 'posted' | 'settled'

export class Expense {
  //@ invariant this.amount >= 0
  //@ invariant sum(this.shares) === this.amount
  //@ invariant this.shares.every(s => s >= 0)
  //@ invariant 0 <= this.payer && this.payer < this.shares.length
  //@ [EXPENSE-LIFECYCLE] lifecycle status: 'draft' -> 'posted' -> 'settled'
  //@ [EXPENSE-LIFECYCLE] lifecycle never status: 'posted' | 'settled' -> 'draft'
  //@ [EXPENSE-LIFECYCLE] lifecycle never status: 'settled' -> 'posted'

  //@ requires amount >= 0
  //@ requires sum(shares) === amount
  //@ requires shares.every(s => s >= 0)
  //@ requires 0 <= payer && payer < shares.length
  constructor(
    public id: string,
    public label: string,
    public payer: int,
    public amount: int,
    public shares: int[],
    public status: Status,
  ) {}

  post(): void {
    //@ raises this.status !== 'draft'
    //@ ensures this.status === 'posted'
    if (this.status !== 'draft') {
      throw new Error('only a draft can be posted')
    }
    this.status = 'posted'
  }

  settle(): void {
    //@ raises this.status !== 'posted'
    //@ ensures this.status === 'settled'
    if (this.status !== 'posted') {
      throw new Error('only a posted expense can be settled')
    }
    this.status = 'settled'
  }
}
