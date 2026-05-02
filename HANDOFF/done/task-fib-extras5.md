# Task — Fibonacci count sanity beyond n=25

**File:** `AnalyticCombinatorics/Examples/Fibonacci.lean` (append)

The file has `fibClass.count n` sanity through `n = 25`. Extend through `n = 28`.

Use the existing helper bridging `fibClass.count` to `Nat.fib` followed by `decide` (or `native_decide` if needed). Compute target values from the Fibonacci recurrence yourself.

If elaboration blows up at some n=k, document the threshold and stop there.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-fib-extras5-reply.md.
- **ONLY modify `AnalyticCombinatorics/Examples/Fibonacci.lean`.** Local instances if needed.
