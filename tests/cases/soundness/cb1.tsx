// A JSX event handler runs whenever the user acts: it is checked on its own,
// for any event and any value of what it captures.

function pos(x: number): number {
  //@ requires x >= 1
  return x - 1;
}

export function Counter(n: number) {
  return <button onClick={() => pos(n)}>go</button>;
}

export function Thrower(n: number) {
  return (
    <button
      onClick={() => {
        if (n < 0) throw new Error("negative");
      }}
    >
      go
    </button>
  );
}
