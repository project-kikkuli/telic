# splitter

A shared-expense splitter (groups, members, expenses, settle-up, a settings
screen) built with telic as its only verification. There are no tests: the
requirements are aims, and telic proves the lemmas under them or shows the
input that breaks one.

- `server/`: plain Python HTTP API (`app.py`) over the domain: `split.py`
  (equal splits), `ledger.py` (balances, settle-up), `expense.py` (the
  expense lifecycle).
- `web/`: TypeScript + Vite, no framework. `split.ts` mirrors the server's
  split for the preview; `expense.ts` has its own lifecycle; `main.ts`
  holds the UI lemmas.
- `aims/`: one EARS sentence per requirement, with `by:` pointing at the
  code that backs it.

## Run it

```bash
cd examples/splitter/web && npm ci && sh dev.sh 5173   # API on 5174, app on http://127.0.0.1:5173
```

## Check it

From `examples/splitter` (the UI lemmas need `pip install 'telic[ui]'` and
`playwright install chromium`):

```bash
telic check                 # everything, including the UI lemmas (about 10 minutes the first time)
telic check --no-ui server  # the Python side only
telic aims                  # the requirements and what backs them
```

## What is proved

| aim | backed by |
|---|---|
| SPLIT-EXACT | `split_equal`: length, sum, no negative share, each share pinned by `share_of`; `split_exact` |
| SPLIT-AGREE | `share_of ≡ shareOf` (symbolic), then `split_equal ≡ splitEqual` from their contracts |
| BALANCE-ZERO | `apply_expense` keeps the sum, `balances` starts from `[0] * members` |
| EXPENSE-LIFECYCLE | `draft -> posted -> settled` and the `never` lines, in Python and TypeScript |
| SETTLE-CLEARS | payments are positive and go from debtors to creditors; "clears every balance" is open |
| BACK-HOME | `always reachable home`, on the model learned from the running app |
| SETTLE-VISIBLE | `unobscured button "Settle up" while not overlay`, hit-tested at 390x844 and 1280x800 |
| CURRENCY-PERSISTS | `persists combobox "Currency"`: changed, reopened, still changed |

## How it was built

1. Aims first: `aims/*.md`, before any code. `telic aims` lists them as
   unbacked and names every `by:` target that does not exist yet.
2. Code with contracts, one module at a time, `telic check <file>` after
   each. Two finds on the way:
   - SETTLE-VISIBLE was refuted: the "Group settled" toast sat on the
     Settle up button at 390x844, with a three-step trace replayed in the
     browser. The toast moved to the top.
   - The loop in `split_equal` needed a per-element invariant; with it, the
     sum invariant timed out, and `telic prove --agent "claude -p"` closed it
     in Lean (`server/split.py.proof.lean`).
3. A mirror between two loops is proved from their contracts when a
   loop-free helper pair (`share_of`, `shareOf`) is mirrored first.

Still open: `parseCents` (what `Number.parseInt` returns is unchecked),
`balances_body` (untyped JSON validated in a loop), and the clearing half of
SETTLE-CLEARS (a sum over a filtered, growing list).
