// Code that once made telic fail with an internal error instead of a
// verdict. `// expect: <verdict>` above each function pins what telic reports.

class Entry {
  label: string;
  amount: number;
  constructor(label: string, amount: number) {
    this.label = label;
    this.amount = amount;
  }
}

// expect: proved
export function load(raw: string): Entry[][] {
  const data = JSON.parse(raw) as { entries: Entry[] }[];
  return data.map((g) => g.entries.map((e) => new Entry(e.label, e.amount)));
}
