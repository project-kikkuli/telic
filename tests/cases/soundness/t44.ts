type int = number;

export function aliasDoesNotAssertIntegrality(n: int): number {
  //@ requires n === 1.5
  //@ ensures Number.isInteger(result)
  return n;
}

export function unsafeCountedLoop(): number {
  //@ ensures result === 0
  for (let i = 9007199254740992; i < 9007199254740994; i++) {}
  return 0;
}
