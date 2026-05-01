# Task — StringsNoConsecutiveOnes count sanity beyond n=6

**File:** `AnalyticCombinatorics/Examples/StringsNoConsecutiveOnes.lean` (append)

The file has `noConsecOnesClass.count n` sanity through `n = 6` (`21`). Extend through `n = 11` matching `Nat.fib (n + 2)`:
- `n = 7`: `34`
- `n = 8`: `55`
- `n = 9`: `89`
- `n = 10`: `144`
- `n = 11`: `233`

Use `noConsecOnesClass_count_eq_fib + decide` (the closed form is already proved).

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-noco-extras-reply.md.
- **ONLY modify `AnalyticCombinatorics/Examples/StringsNoConsecutiveOnes.lean`.** Local instances if needed.
