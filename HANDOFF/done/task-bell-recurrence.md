# Task — Bell number recurrence (state-or-blocker)

**File:** `AnalyticCombinatorics/Examples/SetPartitions.lean` (append)

The Bell number recurrence: `B(n+1) = ∑_{k=0}^{n} C(n, k) · B(k)`. Try to **state** this for `Nat.bell` (or whatever Mathlib name is used in the file).

```lean
theorem bell_recurrence (n : ℕ) :
    Nat.bell (n + 1) = ∑ k ∈ Finset.range (n + 1), Nat.choose n k * Nat.bell k := by
  sorry
```

Search Mathlib first — this might already be in `Mathlib.Combinatorics.Bell` or `Mathlib.Combinatorics.Enumerative.Bell` as a theorem.

If Mathlib has it, just expose it under a project-friendly name. If not, **document the absence** and stop — proving from scratch is substantial.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-bell-recurrence-reply.md.
- If Mathlib doesn't have it, that's a **legitimate blocker**. Document and stop, don't paper over.
- Do NOT introduce axioms.
