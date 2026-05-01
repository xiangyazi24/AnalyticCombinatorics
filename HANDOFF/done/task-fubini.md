# Task — Fubini numbers via labelSeq

**File:** `AnalyticCombinatorics/Examples/SetPartitions.lean` (append at end)

**Goal:** Prove that the labelled SEQ of posIntClass counts ordered set partitions (Fubini / ordered Bell numbers).

```lean
import AnalyticCombinatorics.PartA.Ch1.Sequences  -- already imported via Compositions
import Mathlib.Combinatorics.Enumerative.Stirling

open CombinatorialClass

/-- The labelled SEQ of posIntClass at size n counts ordered set partitions
    of {1..n} (Fubini / ordered Bell number). The closed form is the sum
    ∑_{k=0}^{n} k! · S(n, k). -/
theorem labelSeq_posIntClass_count_eq_fubini (n : ℕ) :
    (labelSeq posIntClass posIntClass.count_zero).count n =
      ∑ k ∈ Finset.range (n + 1), k.factorial * Nat.stirlingSecond n k := by
  rw [labelSeq.count_eq]
  apply Finset.sum_congr rfl
  intro k _
  exact labelPow_posIntClass_count_eq_factorial_mul_stirlingSecond n k

/-! Sanity: Fubini numbers are 1, 1, 3, 13, 75, 541, 4683.
    a(0) = ∑ k ∈ range 1, k! · S(0,k) = 1.
    a(1) = ∑ k ∈ range 2, k! · S(1,k) = 1.
    a(2) = ∑ k ∈ range 3, k! · S(2,k) = 0!·0 + 1!·1 + 2!·1 = 3.
    a(3) = 0!·0 + 1!·1 + 2!·3 + 3!·1 = 1 + 6 + 6 = 13. -/
example : (labelSeq posIntClass posIntClass.count_zero).count 0 = 1 := by
  rw [labelSeq_posIntClass_count_eq_fubini]; decide
example : (labelSeq posIntClass posIntClass.count_zero).count 1 = 1 := by
  rw [labelSeq_posIntClass_count_eq_fubini]; decide
example : (labelSeq posIntClass posIntClass.count_zero).count 2 = 3 := by
  rw [labelSeq_posIntClass_count_eq_fubini]; decide
example : (labelSeq posIntClass posIntClass.count_zero).count 3 = 13 := by
  rw [labelSeq_posIntClass_count_eq_fubini]; decide
```

Use `native_decide` if `decide` is too slow.

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-fubini-reply.md
