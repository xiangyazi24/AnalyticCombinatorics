# Task — Fubini coefficient form

**File:** `AnalyticCombinatorics/Examples/SetPartitions.lean` (append)

**Goal:** Direct EGF coefficient identity for labelSeq posIntClass (Fubini = ordered Bell).

```lean
example (n : ℕ) :
    (CombinatorialClass.labelSeq posIntClass posIntClass.count_zero).count n =
      ∑ k ∈ Finset.range (n + 1), k.factorial * Nat.stirlingSecond n k :=
  labelSeq_posIntClass_count_eq_fubini n
```

If already there, file blocker / no-op.

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-fubini-coeff-reply.md
