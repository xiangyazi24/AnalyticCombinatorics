# Task — Derangements sanity 7, 8

**File:** `AnalyticCombinatorics/Examples/Derangements.lean` (append)

```lean
example : derangementClass.count 7 = 1854 := by
  rw [derangementClass_count_eq_numDerangements]; decide
example : derangementClass.count 8 = 14833 := by
  rw [derangementClass_count_eq_numDerangements]; decide
```

Use `native_decide` if `decide` is too slow.

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-derangement-sanity-more-reply.md
