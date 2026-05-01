# Task — Catalan number recurrence

**File:** `AnalyticCombinatorics/Examples/CatalanFamily.lean` (append) [or wherever cleanest — pick the file with the most existing `Nat.catalan` use]

The classical Catalan recurrence:

`C(n+1) = ∑_{i=0}^{n} C(i) · C(n-i)`

Try to **state and prove**:

```lean
theorem catalan_recurrence (n : ℕ) :
    Nat.catalan (n + 1) = ∑ i ∈ Finset.range (n + 1), Nat.catalan i * Nat.catalan (n - i) := by
  sorry
```

Almost certainly already in Mathlib as `Nat.catalan_succ` or `Nat.catalan_succ'`. Search; expose if found, document blocker if not.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-catalan-rec-reply.md.
- Pick whichever file is the most natural home — I'll trust your call.
- Do NOT introduce axioms.
