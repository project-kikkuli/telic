export type int = number

export function shareOf(amount: int, parts: int, index: int): int {
  //@ [SPLIT-AGREE] mirrors ../../server/split.py::share_of
  //@ requires amount >= 0
  //@ requires parts >= 1
  //@ requires 0 <= index && index < parts
  //@ ensures result >= 0
  const base = Math.floor(amount / parts)
  return index < amount % parts ? base + 1 : base
}

export function splitEqual(amount: int, parts: int): int[] {
  //@ [SPLIT-AGREE] mirrors ../../server/split.py::split_equal
  //@ requires amount >= 0
  //@ requires parts >= 1
  //@ ensures result.length === parts
  //@ ensures range(0, parts).every(i => result[i] === shareOf(amount, parts, i))
  const shares: int[] = []
  for (let i = 0; i < parts; i++) {
    //@ invariant shares.length === i
    //@ invariant range(0, i).every(k => shares[k] === shareOf(amount, parts, k))
    shares.push(shareOf(amount, parts, i))
  }
  return shares
}

export function parseCents(text: string): int | undefined {
  //@ ensures result === undefined || result >= 0
  const m = /^\s*(\d+)(?:[.,](\d{1,2}))?\s*$/.exec(text)
  if (m === null) {
    return undefined
  }
  const whole = Number.parseInt(m[1], 10)
  const frac = m[2] === undefined ? 0 : Number.parseInt(m[2].padEnd(2, '0'), 10)
  return whole * 100 + frac
}
