# Task — StringsNoConsecutiveOnes count sanity beyond n=15

**File:** `AnalyticCombinatorics/Examples/StringsNoConsecutiveOnes.lean` (append)

The file has `noConsecOnesClass.count n` sanity through `n = 15` (`1597`). Extend through `n = 18` matching `Nat.fib (n + 2)`:
- `n = 16`: `2584`
- `n = 17`: `4181`
- `n = 18`: `6765`

Use `noConsecOnesClass_count_eq_fib + decide`.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-noco-extras3-reply.md.
- **ONLY modify `AnalyticCombinatorics/Examples/StringsNoConsecutiveOnes.lean`.** Local instances if needed.
