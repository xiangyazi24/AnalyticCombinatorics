# Task — Fubini sanity 7, 8

**File:** `AnalyticCombinatorics/Examples/SetPartitions.lean` (append)

Fubini sequence: 1, 1, 3, 13, 75, 541, 4683, 47293, 545835.

```lean
example : (CombinatorialClass.labelSeq posIntClass posIntClass.count_zero).count 7 = 47293 := by
  rw [labelSeq_posIntClass_count_eq_fubini]; decide
example : (CombinatorialClass.labelSeq posIntClass posIntClass.count_zero).count 8 = 545835 := by
  rw [labelSeq_posIntClass_count_eq_fubini]; decide
```

Use `native_decide` if needed.

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-fubini-sanity-more-reply.md
