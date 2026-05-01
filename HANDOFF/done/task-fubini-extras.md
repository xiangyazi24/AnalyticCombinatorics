# Task — Fubini extras

**File:** `AnalyticCombinatorics/Examples/SetPartitions.lean` (append at end)

**Goal:** Add Fubini numbers 4, 5, 6 sanity. Sequence: 1, 1, 3, 13, 75, 541, 4683.

```lean
example : (labelSeq posIntClass posIntClass.count_zero).count 4 = 75 := by
  rw [labelSeq_posIntClass_count_eq_fubini]; decide
example : (labelSeq posIntClass posIntClass.count_zero).count 5 = 541 := by
  rw [labelSeq_posIntClass_count_eq_fubini]; decide
example : (labelSeq posIntClass posIntClass.count_zero).count 6 = 4683 := by
  rw [labelSeq_posIntClass_count_eq_fubini]; decide
```

If `decide` is too slow, use `native_decide` or compute via `Nat.bell_succ'`-style chains.

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-fubini-extras-reply.md
