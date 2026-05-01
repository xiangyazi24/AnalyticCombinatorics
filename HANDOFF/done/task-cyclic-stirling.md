# Task — labelCycCount posIntClass formula via Stirling

**File:** `AnalyticCombinatorics/Examples/SetPartitions.lean` (append)

**Goal:** Use the existing labelPow_posIntClass_count_eq_factorial_mul_stirlingSecond bridge to give a formula for labelCycCount posIntClass:

```lean
example (n : ℕ) :
    CombinatorialClass.labelCycCount posIntClass n =
      ∑ k ∈ Finset.range (n + 1),
        if k = 0 then 0
        else ((k - 1).factorial * Nat.stirlingSecond n k : ℚ) := by
  unfold CombinatorialClass.labelCycCount
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k = 0
  · simp [hk]
  · have hk' : 0 < k := Nat.pos_of_ne_zero hk
    rw [if_neg hk, if_neg hk]
    rw [labelPow_posIntClass_count_eq_factorial_mul_stirlingSecond]
    push_cast
    rw [show (k.factorial : ℚ) = k * (k-1).factorial from by
      rw [show k = (k-1) + 1 from by omega, Nat.factorial_succ]; push_cast; ring]
    field_simp
    ring
```

If the manipulation is fragile, simplify or file blocker.

## Hard constraints

- Build green
- No new sorrys when delivered (or file blocker)
- Reply at HANDOFF/outbox/task-cyclic-stirling-reply.md
