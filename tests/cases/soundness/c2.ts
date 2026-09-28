type int = number;
export function down(n: int): int {
  let s = 0;
  for (let i = n; i > 0; i--) {
    s++;
  }
  return s;
}
export function other(): int { return 1; }
