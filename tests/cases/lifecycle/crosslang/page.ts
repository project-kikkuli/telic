export class Order {
  //@ lifecycle monotonic this.paid
  constructor(public paid: number) {}

  pay(amount: number): void {
    //@ requires amount >= 0 && Number.isFinite(amount)
    this.paid = this.paid + amount
  }
}

// Unsupported: it may change a TypeScript Order, never a Python one.
export function refresh(o: Order): void {
  var paid = o.paid
  o.paid = paid
}
