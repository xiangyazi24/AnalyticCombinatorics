# Task — Fibonacci compositions sanity beyond n=12

**File:** `AnalyticCombinatorics/Examples/Fibonacci.lean` (append)

The file has `fibClass.count n` sanity at `n = 0..12`. Push further: add `n = 13..18` matching the corresponding Fibonacci numbers via `fibClass_count_eq_fib`.

Compute the values:
- `fibClass.count 13 = Nat.fib 14 = 377`
- `fibClass.count 14 = Nat.fib 15 = 610`
- `fibClass.count 15 = Nat.fib 16 = 987`
- `fibClass.count 16 = Nat.fib 17 = 1597`
- `fibClass.count 17 = Nat.fib 18 = 2584`
- `fibClass.count 18 = Nat.fib 19 = 4181`

Use the same tactic the existing examples use. Switch to `native_decide` if needed.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-fib-extras-reply.md.
