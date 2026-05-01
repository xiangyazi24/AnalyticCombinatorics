# Task — Derangement sanity beyond D_15

**File:** `AnalyticCombinatorics/Examples/Derangements.lean` (append)

The file has `derangementClass.count n = Nat.numDerangements n` sanity through `D_15`. Extend through `D_18`:
- `D_16 = 7697064251745`
- `D_17 = 130850092279664`
- `D_18 = 2355301661033953`

Use the existing `derangementClass_count_eq_numDerangements + decide` pattern. Switch to `native_decide` if needed.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-derange-extras3-reply.md.
- **ONLY modify `AnalyticCombinatorics/Examples/Derangements.lean`.** Local instances if needed.
