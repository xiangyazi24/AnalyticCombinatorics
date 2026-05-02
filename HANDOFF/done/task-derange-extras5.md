# Task — derangement count sanity beyond D_21

**File:** `AnalyticCombinatorics/Examples/Derangements.lean` (append)

The file has `derangementClass.count n` sanity through `n = 21`. Extend through `n = 24`.

Use the existing helper `derangementClass_count_eq_numDerangements` followed by `decide` / `native_decide` (match the surrounding pattern). Compute the targets from the recurrence `D(n) = (n-1)·(D(n-1)+D(n-2))` with `D(20) = 895014631192902121`, `D(21) = 18795307255050944540`.

If elaboration blows up at some n=k, document the threshold and stop there.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-derange-extras5-reply.md.
- **ONLY modify `AnalyticCombinatorics/Examples/Derangements.lean`.** Local instances if needed.
