# Task — Derangement sanity checks

**File:** `AnalyticCombinatorics/Examples/Derangements.lean` (append at end)

**Goal:** Add sanity checks: numDerangements 0..6 = 1, 0, 1, 2, 9, 44, 265.

```lean
example : derangementClass.count 0 = 1 := by
  rw [derangementClass_count_eq_numDerangements]; decide
example : derangementClass.count 1 = 0 := by
  rw [derangementClass_count_eq_numDerangements]; decide
example : derangementClass.count 2 = 1 := by
  rw [derangementClass_count_eq_numDerangements]; decide
example : derangementClass.count 3 = 2 := by
  rw [derangementClass_count_eq_numDerangements]; decide
example : derangementClass.count 4 = 9 := by
  rw [derangementClass_count_eq_numDerangements]; decide
example : derangementClass.count 5 = 44 := by
  rw [derangementClass_count_eq_numDerangements]; decide
```

Use `native_decide` if `decide` is too slow. Use whatever name `Nat.numDerangements` was bridged to.

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-derangements-sanity-reply.md
