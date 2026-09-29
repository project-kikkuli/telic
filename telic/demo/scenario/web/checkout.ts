// Checkout page math. Ported from server/billing.py by an AI, same night.

export function displayTotal(subtotal: number, percent: number): number {
  //@ requires Number.isInteger(subtotal) && Number.isInteger(percent)
  //@ requires subtotal >= 0 && 0 <= percent && percent <= 100
  //@ aim PRICE-AGREE
  //@ mirrors ../server/billing.py::discounted_total
  //@ ensures 0 <= result && result <= subtotal
  return subtotal - Math.round((subtotal * percent) / 100);
}
