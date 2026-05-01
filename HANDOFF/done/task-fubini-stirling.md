# Task — Fubini = ∑ k! · Stirling 2nd

**File:** `AnalyticCombinatorics/Examples/SetPartitions.lean` (append)

**Goal:** Restate Fubini in a slightly different form already covered by labelSeq_posIntClass_count_eq_fubini.

```lean
example (n : ℕ) :
    (CombinatorialClass.labelSeq posIntClass posIntClass.count_zero).count n =
      ∑ k ∈ Finset.range (n + 1), k.factorial * Nat.stirlingSecond n k :=
  labelSeq_posIntClass_count_eq_fubini n
```

If already there, file noop.

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-fubini-stirling-reply.md
