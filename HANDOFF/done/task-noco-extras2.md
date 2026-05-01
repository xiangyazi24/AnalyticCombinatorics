# Task — StringsNoConsecutiveOnes count sanity beyond n=11

**File:** `AnalyticCombinatorics/Examples/StringsNoConsecutiveOnes.lean` (append)

The file has `noConsecOnesClass.count n` sanity through `n = 11` (`233`). Extend through `n = 15` matching `Nat.fib (n + 2)`:
- `n = 12`: `377`
- `n = 13`: `610`
- `n = 14`: `987`
- `n = 15`: `1597`

Use `noConsecOnesClass_count_eq_fib + decide`.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-noco-extras2-reply.md.
- **ONLY modify `AnalyticCombinatorics/Examples/StringsNoConsecutiveOnes.lean`.** Local instances if needed.
