# Task — Derangement recurrence

**File:** `AnalyticCombinatorics/Examples/Derangements.lean` (append)

The classical derangement recurrence: `D(n+2) = (n+1) · (D(n+1) + D(n))`. Try to **state and prove**:

```lean
theorem numDerangements_recurrence (n : ℕ) :
    Nat.numDerangements (n + 2) = (n + 1) * (Nat.numDerangements (n + 1) + Nat.numDerangements n) := by
  sorry
```

Almost certainly already in Mathlib as `Nat.numDerangements_add_two` or similar. Search; expose if found. If not, document the absence.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-derange-rec-reply.md.
- Do NOT introduce axioms.
