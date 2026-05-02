# Task — PlaneTree count sanity beyond n=18

**File:** `AnalyticCombinatorics/Examples/PlaneTrees.lean` (append)

The file has `planeTreeClass.count n` sanity through `n = 18` (matching Catalan numbers). Extend through `n = 21`.

Catalan: C_19 = 1767263190, C_20 = 6564120420, C_21 = 24466267020.

Use the existing helper bridging planeTree count to Catalan followed by `decide` / `native_decide` matching the surrounding pattern.

If elaboration blows up at some n=k, document the threshold and stop there.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-planetree-extras1-reply.md.
- **ONLY modify `AnalyticCombinatorics/Examples/PlaneTrees.lean`.** Local instances if needed.
