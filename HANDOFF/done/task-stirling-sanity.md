# Task — Stirling 2nd kind sanity via labelPow posIntClass

**File:** `AnalyticCombinatorics/Examples/SetPartitions.lean` (append at end)

**Goal:** Concrete sanity checks combining the Stirling bridge with small values of n, k.

```lean
/-! Sanity: ordered set partitions count = k! · S(n,k).
    S(2,1) = 1, S(2,2) = 1.
    S(3,1) = 1, S(3,2) = 3, S(3,3) = 1.
    S(4,2) = 7, S(4,3) = 6.
-/

example : (CombinatorialClass.labelPow posIntClass 1).count 2 = 0 := by
  rw [labelPow_posIntClass_count_eq_factorial_mul_stirlingSecond]
  -- 1! · S(2,1) = 1 · 1 = 1, but count of (labelPow posIntClass 1).count 2:
  -- Wait, that's S(2,1) = 1, so 1! · 1 = 1. Hmm, this should be 1 not 0.
  -- Actually labelPow posIntClass 1 = posIntClass.labelProd Epsilon ≅ posIntClass.
  -- posIntClass.count 2 = 1. So count 2 = 1, matches 1! · S(2,1) = 1.
  -- (Adjust expected RHS in this example to 1.)
  decide

example : (CombinatorialClass.labelPow posIntClass 2).count 3 = 6 := by
  rw [labelPow_posIntClass_count_eq_factorial_mul_stirlingSecond]
  -- 2! · S(3,2) = 2 · 3 = 6.
  decide

example : (CombinatorialClass.labelPow posIntClass 3).count 4 = 36 := by
  rw [labelPow_posIntClass_count_eq_factorial_mul_stirlingSecond]
  -- 3! · S(4,3) = 6 · 6 = 36.
  decide
```

Adapt expected values as needed; use `native_decide` if `decide` is too slow.

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-stirling-sanity-reply.md
