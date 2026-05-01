# Task — Bell number sanity checks

**File:** `AnalyticCombinatorics/Examples/SetPartitions.lean` (append at end)

**Goal:** Add concrete sanity checks for `labelSetCount posIntClass n` matching small Bell numbers.

```lean
/-! Sanity checks: Bell sequence starts 1, 1, 2, 5, 15, 52, 203, ... -/
example : labelSetCount posIntClass 0 = (1 : ℚ) := by
  rw [labelSetCount_posIntClass_eq_bell]; rfl
example : labelSetCount posIntClass 1 = (1 : ℚ) := by
  rw [labelSetCount_posIntClass_eq_bell]; decide
example : labelSetCount posIntClass 2 = (2 : ℚ) := by
  rw [labelSetCount_posIntClass_eq_bell]; decide
example : labelSetCount posIntClass 3 = (5 : ℚ) := by
  rw [labelSetCount_posIntClass_eq_bell]; decide
example : labelSetCount posIntClass 4 = (15 : ℚ) := by
  rw [labelSetCount_posIntClass_eq_bell]; decide
```

If `decide` doesn't reduce, try `native_decide` or `Nat.bell_succ' ; rfl`-chain. Adapt as needed but no sorrys.

## Hard constraints

- Build green
- Reply at HANDOFF/outbox/task-bell-sanity-reply.md
