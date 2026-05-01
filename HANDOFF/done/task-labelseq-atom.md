# Task — labelSeq Atom count = n! (= permClass.count)

**File:** `AnalyticCombinatorics/PartA/Ch2/LabelledClass.lean` (append at end)

**Goal:** Compute the count of `labelSeq Atom`. Should equal `n!` since each labelled sequence of size-1 atoms is a permutation.

```lean
/-- The labelled SEQ of unit atoms has the same count as permutations: count n = n!. -/
theorem labelSeq_Atom_count (n : ℕ) :
    (CombinatorialClass.labelSeq Atom Atom_count_zero).count n = n.factorial := by
  rw [CombinatorialClass.labelSeq.count_eq]
  -- ∑ k ∈ range (n+1), (labelPow Atom k).count n
  -- by labelPow_Atom_count: count = if n = k then n! else 0
  -- only k = n contributes
  rw [Finset.sum_eq_single n]
  · simp [labelPow_Atom_count]
  · intro k _ hk
    rw [labelPow_Atom_count]
    rw [if_neg (Ne.symm hk)]
  · intro h
    exfalso; apply h; simp

/-- Therefore labelSeq Atom and permClass have the same count function. -/
example (n : ℕ) :
    (CombinatorialClass.labelSeq Atom Atom_count_zero).count n = permClass.count n := by
  rw [labelSeq_Atom_count, permClass_count_eq_factorial]
```

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-labelseq-atom-reply.md
