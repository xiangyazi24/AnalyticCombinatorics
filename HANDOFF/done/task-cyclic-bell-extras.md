# Task — cyclic Fubini sanity 5..7

**File:** `AnalyticCombinatorics/Examples/SetPartitions.lean` (append)

```lean
example : CombinatorialClass.labelCycCount posIntClass 5 = (150 : ℚ) := by
  rw [labelCycCount_posIntClass_eq_cyclic_fubini]
  decide
example : CombinatorialClass.labelCycCount posIntClass 6 = (1082 : ℚ) := by
  rw [labelCycCount_posIntClass_eq_cyclic_fubini]
  decide
example : CombinatorialClass.labelCycCount posIntClass 7 = (9366 : ℚ) := by
  rw [labelCycCount_posIntClass_eq_cyclic_fubini]
  decide
```

Use `native_decide` if needed. Match whatever the existing bridge theorem is named.

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-cyclic-bell-extras-reply.md
