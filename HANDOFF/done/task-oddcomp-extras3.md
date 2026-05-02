# Task — Odd-composition count sanity beyond n=16

**File:** `AnalyticCombinatorics/Examples/CompositionsOdd.lean` (append)

The file has `oddCompClass.count n` sanity through `n = 16` (`987`). Extend through `n = 20`:
- `count 17 = 1597`
- `count 18 = 2584`
- `count 19 = 4181`
- `count 20 = 6765`

Use `oddCompClass_count_succ_eq_fib + decide`.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-oddcomp-extras3-reply.md.
- **ONLY modify `AnalyticCombinatorics/Examples/CompositionsOdd.lean`.** Local instances if needed.
