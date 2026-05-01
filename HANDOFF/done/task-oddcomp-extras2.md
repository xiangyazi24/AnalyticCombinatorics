# Task — Odd-composition count sanity beyond n=12

**File:** `AnalyticCombinatorics/Examples/CompositionsOdd.lean` (append)

The file has `oddCompClass.count n` sanity through `n = 12` (`144`). Extend through `n = 16` matching `Nat.fib`:
- `count 13 = 233`
- `count 14 = 377`
- `count 15 = 610`
- `count 16 = 987`

Use `oddCompClass_count_succ_eq_fib + decide`.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-oddcomp-extras2-reply.md.
- **ONLY modify `AnalyticCombinatorics/Examples/CompositionsOdd.lean`.** Local instances if needed.
