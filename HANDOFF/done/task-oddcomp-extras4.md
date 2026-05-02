# Task — Odd Compositions sanity beyond n=20

**File:** `AnalyticCombinatorics/Examples/CompositionsOdd.lean` (append)

The file currently has `oddCompClass.count` sanity through around n=20. Extend through n=23.

Odd compositions of n (parts all odd) satisfy oddCompClass.count(n+1) = F(n) (Fibonacci). Use OEIS A000045 for values.

Use the same proof shape as existing entries.

If `native_decide` times out at some n, document the threshold and stop there.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-oddcomp-extras4-reply.md.
- **ONLY modify `AnalyticCombinatorics/Examples/CompositionsOdd.lean`.** Local instances if needed.
