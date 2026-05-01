# Task — bellSeries coeff form

**File:** `AnalyticCombinatorics/Examples/SetPartitions.lean` (append)

**Goal:** A direct coefficient identity for the bellSeries / labelSetSeries.

```lean
example (n : ℕ) :
    labelSetCount posIntClass n / (n.factorial : ℚ) =
      (Nat.bell n : ℚ) / n.factorial := by
  rw [labelSetCount_posIntClass_eq_bell]
```

If `labelSetCount_posIntClass_eq_bell` already does this directly, just check or refactor.

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-bell-coeff-reply.md
