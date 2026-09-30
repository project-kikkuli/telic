// A JavaScript string is UTF-16 code units: an emoji is two of them.
type int = number;
export function emojiLength(): int {
  //@ ensures result === 1
  return "😀".length;
}

export function emojiAfterBmp(): boolean {
  //@ ensures result
  return "￿" < "😀";
}
