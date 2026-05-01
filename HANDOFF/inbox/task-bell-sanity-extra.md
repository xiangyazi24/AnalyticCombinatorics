# Task — Bell sanity extra

**File:** `AnalyticCombinatorics/Examples/SetPartitions.lean` (append at end)

**Goal:** Add Bell numbers 5, 6, 7 sanity. Bell sequence: 1, 1, 2, 5, 15, 52, 203, 877.

```lean
example : labelSetCount posIntClass 5 = (52 : ℚ) := by
  rw [labelSetCount_posIntClass_eq_bell]; decide
example : labelSetCount posIntClass 6 = (203 : ℚ) := by
  rw [labelSetCount_posIntClass_eq_bell]; decide
example : labelSetCount posIntClass 7 = (877 : ℚ) := by
  rw [labelSetCount_posIntClass_eq_bell]; decide
```

Use `native_decide` if `decide` is too slow.

## Hard constraints

- Build green; no new sorrys
- Reply at HANDOFF/outbox/task-bell-sanity-extra-reply.md
