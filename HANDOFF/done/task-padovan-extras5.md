# Task — Padovan count sanity beyond n=24

**File:** `AnalyticCombinatorics/Examples/Padovan.lean` (append)

The file has `padovanClass.count n` sanity through `n = 24`. Extend through `n = 27`.

Use the existing helper bridging `padovanClass.count` to the Padovan sequence (`P(n) = P(n-2)+P(n-3)`) followed by `decide` / `native_decide` matching the surrounding pattern. Compute the targets yourself.

If elaboration blows up at some n=k, document the threshold and stop there.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-padovan-extras5-reply.md.
- **ONLY modify `AnalyticCombinatorics/Examples/Padovan.lean`.** Local instances if needed.
