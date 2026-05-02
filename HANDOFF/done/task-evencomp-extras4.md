# Task — Even Compositions sanity beyond n=22

**File:** `AnalyticCombinatorics/Examples/CompositionsEven.lean` (append)

The file currently has `evenCompClass.count` sanity through around n=22. Extend through n=28.

Even compositions of 2k equal compositions of k, so evenCompClass.count(2k) = 2^(k-1) for k ≥ 1, and evenCompClass.count(2k+1) = 0.

Use the same proof shape as existing entries.

If `native_decide` times out at some n, document the threshold and stop there.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-evencomp-extras4-reply.md.
- **ONLY modify `AnalyticCombinatorics/Examples/CompositionsEven.lean`.** Local instances if needed.
