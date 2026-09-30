import { v4 as uuid } from "uuid";

export enum Status {
  Draft = "draft",
  Paid = "paid",
  Shipped = "shipped",
}

type int = number;

export interface Item {
  sku: string;
  priceCents: int;
  qty: int;
  note?: string;
}

const MAX_ITEMS = 50;

export class Cart {
  //@ invariant this.totalCents >= 0 && Number.isSafeInteger(this.totalCents)
  items: Item[] = [];
  status: Status = Status.Draft;
  totalCents: int = 0;
  readonly id: string;

  constructor(public owner: string) {
    this.id = uuid();
  }

  add(item: Item): void {
    //@ requires item.priceCents >= 0 && item.qty > 0
    //@ ensures this.totalCents >= old(this.totalCents)
    if (this.items.length >= MAX_ITEMS) {
      throw new Error(`cart ${this.id} is full`);
    }
    this.items.push(item);
    this.totalCents += item.priceCents * item.qty;
  }

  pay(ref: string): void {
    //@ requires this.status === Status.Draft
    //@ ensures this.status === Status.Paid
    this.status = Status.Paid;
  }

  get label(): string {
    return `${this.owner.toUpperCase()}: ${this.status} (${this.items.length} items)`;
  }
}

export function withTax(cents: int): int {
  //@ requires cents >= 0 && Number.isSafeInteger(cents)
  //@ ensures result >= cents
  return cents + Math.floor((cents * 8) / 100);
}

export function discount(total: number, code: string | undefined, codes: Map<string, number>): number {
  //@ requires total >= 0
  //@ ensures 0 <= result && result <= total
  if (code === undefined || !codes.has(code)) return total;
  const pct = codes.get(code)!;
  return total - (total * pct) / 100;
}

export function noteLength(item: Item): number {
  return item.note?.length ?? 0;
}

export function badNote(item: Item): number {
  return item.note!.length;
}

export async function checkout(cart: Cart, gateway: any): Promise<boolean> {
  //@ requires cart.status === Status.Draft
  const ok = await gateway.charge(cart.owner, withTax(cart.totalCents));
  if (ok) {
    cart.pay("ref");
    return true;
  }
  return false;
}

export function summarize(carts: Cart[]): Map<string, number> {
  const out = new Map<string, number>();
  for (const c of carts) {
    out.set(c.owner, (out.get(c.owner) ?? 0) + c.totalCents);
  }
  return out;
}

export function skus(cart: Cart): string[] {
  //@ ensures result.length === cart.items.length
  return cart.items.map((i) => i.sku);
}

export function statusLabel(s: Status): string {
  switch (s) {
    case Status.Draft:
      return "draft";
    case Status.Paid:
      return "paid";
    default:
      return "shipped";
  }
}

export function parseQty(raw: unknown): number {
  //@ ensures result >= 1
  try {
    const q = Number(raw);
    return Math.max(q, 1);
  } catch (e) {
    return 1;
  }
}

export function totalPrice(items: Item[]): number {
  let sum = 0;
  items.forEach((it) => {
    sum += it.priceCents * it.qty;
  });
  return sum;
}
