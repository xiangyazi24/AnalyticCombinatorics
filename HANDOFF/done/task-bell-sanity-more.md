# Task — Bell sanity 8, 9, 10

**File:** `AnalyticCombinatorics/Examples/SetPartitions.lean` (append)

Bell numbers: 1, 1, 2, 5, 15, 52, 203, 877, 4140, 21147, 115975.

```lean
example : labelSetCount posIntClass 8 = (4140 : ℚ) := by
  rw [labelSetCount_posIntClass_eq_bell]; decide
example : labelSetCount posIntClass 9 = (21147 : ℚ) := by
  rw [labelSetCount_posIntClass_eq_bell]; decide
example : labelSetCount posIntClass 10 = (115975 : ℚ) := by
  rw [labelSetCount_posIntClass_eq_bell]; decide
```

Use `native_decide` if needed.

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-bell-sanity-more-reply.md
