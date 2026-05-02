# Task — Tribonacci count sanity beyond n=25

**File:** `AnalyticCombinatorics/Examples/Tribonacci.lean` (append)

The file has `tribClass.count n` sanity through `n = 25`. Extend through `n = 28`.

Use the existing helper bridging `tribClass.count` to the Tribonacci sequence (`T(n) = T(n-1)+T(n-2)+T(n-3)`) followed by `decide` / `native_decide` matching the surrounding pattern. Compute the targets yourself.

If elaboration blows up at some n=k, document the threshold and stop there.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-trib-extras5-reply.md.
- **ONLY modify `AnalyticCombinatorics/Examples/Tribonacci.lean`.** Local instances if needed.
