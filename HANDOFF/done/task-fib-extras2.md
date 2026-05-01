# Task — Fibonacci compositions sanity beyond n=18

**File:** `AnalyticCombinatorics/Examples/Fibonacci.lean` (append)

The file has `fibClass.count n` sanity through `n = 18` (`fib 19 = 4181`). Extend through `n = 22`:
- `n = 19`: `fib 20 = 6765`
- `n = 20`: `fib 21 = 10946`
- `n = 21`: `fib 22 = 17711`
- `n = 22`: `fib 23 = 28657`

Use the existing `rw [fibClass_count_eq_fib]; decide` pattern.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-fib-extras2-reply.md.
- **ONLY modify `AnalyticCombinatorics/Examples/Fibonacci.lean`.** Local instances if needed.
