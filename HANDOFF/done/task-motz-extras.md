# Task — Motzkin count sanity beyond size 8

**File:** `AnalyticCombinatorics/Examples/MotzkinTrees.lean` (append)

The file has Motzkin count sanity through size 8 (`323`). Extend through size 12 matching:
- `count 9 = 835`
- `count 10 = 2188`
- `count 11 = 5798`
- `count 12 = 15511`

(File convention: size = #edges, so these match OEIS A001006 at n = 9..12.)

Use the existing `decide` / `rw recurrence` pattern. Switch to `native_decide` if needed.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-motz-extras-reply.md.
