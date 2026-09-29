# Field notes: telic on real apps

telic was run, unmodified and with no contracts added, on four open-source
apps shaped like typical generated code: CRUD backends and a React front end.

| app | stack | before | after | time |
|---|---|---|---|---|
| fastapi-realworld-example-app | FastAPI, pydantic, asyncpg | frontend crash; then 14 false refutations, 37 problems, 28 unsupported | 8 proved, 96 with nothing to check | 0.8s |
| full-stack-fastapi-template (backend) | FastAPI, SQLModel | 2 false refutations, 1 unsupported | 7 proved, 49 with nothing to check, 1 file in Python 3.14 syntax | 0.5s |
| node-express-realworld-example-app | Express, Prisma | 7 unsupported, 1 problem, 1 spurious error | 7 proved, 24 with nothing to check | 0.7s |
| chatbot-ui (lib/, components/utility) | Next.js, React | 17 unsupported, 9 problems | 11 proved, 36 with nothing to check, **1 real crash** | 2.0s |

"Before" is telic as it was when these runs started. Each gap found was fixed
in the frontends or engines, with a regression case or soundness exploit
added to the test suite.

## What it found

`adaptMessagesForGeminiVision([])` in chatbot-ui reads `messages[0].parts`
without checking for an empty list. telic reports it and replays it in Node.

## What the gaps were

Mostly idioms, not deep semantics:

- class inheritance, pydantic models, and library base classes;
- `x or default`, `str + str`, `xs + ys`, `f(**kw)`, JSON-like dict literals;
- empty `[]`/`{}` typed by their first use;
- generators;
- JSX, destructured props, `push(...xs)`, `map` with any callback;
- `let x;`.

A few were soundness bugs, now fixed:

- an overridden method used as a logical definition;
- `await` assuming invariants across shared field maps;
- an uninterpreted function used at two signatures, which made z3 reject
  the query.

## What it means

Most functions in glue code have **nothing to check**. They have no contract
and no operation that can fail, and telic now says so instead of calling
them "proved". The trusted base lists what the rest relies on: every
library call, and that values from libraries have their annotated types.

Silence is the right default for code that makes no claims:

- an intentional `raise HTTPException` is not a bug;
- neither is a `while (true)` stream reader.

telic becomes useful once aims and contracts state what the app must do.
The proofs are only as strong as the claims they prove.
