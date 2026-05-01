# Task — Labelled CYC count + EGF identity

**File:** `AnalyticCombinatorics/PartA/Ch2/LabelledClass.lean` (append at end)

**Goal:** Prove the labelled-CYC count and EGF identity:

```
labelCycCount(B)(n) = ∑_{k=1}^n (1/k) · (labelPow B k).count n   (rational)
EGF(labelCYC(B))(z) = log(1 / (1 - B.egf(z)))
```

This is F&S Theorem II.3 (the third pillar of labelled symbolic method, after labelled product and labelled SET).

## Required code

```lean
/-- Labelled CYC coefficient (rational): the number of labelled cycles
    of B-objects of total size n, where each k-cycle is counted with
    weight 1/k (since cyclic rotations of a k-tuple represent the same cycle). -/
noncomputable def labelCycCount (B : CombinatorialClass) (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1), if k = 0 then 0 else
    ((labelPow B k).count n : ℚ) / (k : ℚ)

/-- The labelled CYC count divided by n! equals the partial-log coefficient. -/
theorem labelCycCount_div_factorial_eq_partial_log_coeff
    (B : CombinatorialClass) (n : ℕ) :
    labelCycCount B n / n.factorial =
      ∑ k ∈ Finset.range (n + 1), if k = 0 then 0 else
        coeff n ((B.egf : PowerSeries ℚ) ^ k) / (k : ℚ) := by
  sorry  -- per-k: ((labelPow B k).count n / k) / n! = coeff n (B.egf^k) / k
         -- via labelPow_count_div_factorial_eq_coeff_pow
```

## Strategy

Same pattern as `labelSetCount_div_factorial_eq_partial_exp_coeff` but with `1/k` weight instead of `1/k!`.

For each k ≥ 1: 
  ((labelPow B k).count n / k) / n!
= ((labelPow B k).count n / n!) / k
= coeff n (B.egf^k) / k         (by labelPow_count_div_factorial_eq_coeff_pow)

The k = 0 case contributes 0 on both sides (the `if k = 0 then 0`).

## Hard constraints

- `lake build` green; current 2771 jobs.
- No new sorrys when delivered.
- Reply at HANDOFF/outbox/task-labelled-cyc-reply.md.
