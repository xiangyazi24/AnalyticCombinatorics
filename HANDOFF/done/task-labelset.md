# Task — Labelled SET partial-sum identity (toward EGF = exp(B.egf))

**File:** `AnalyticCombinatorics/PartA/Ch2/LabelledClass.lean` (append)

**Goal:** Establish the coefficient-level identity that links labelled-SET counts (as rational sums) to coefficients of `∑_{k≤n} (B.egf)^k / k!`. This is the labelled SET → exp identity, F&S Theorem II.2, in coefficient form.

## Setup

A labelled SET of B at size n with k unordered blocks has count `(labelPow B k).count n / k!` (rational). Sum over k:

```
labelSetCount(B)(n) := ∑_{k=0}^{n} (labelPow B k).count n / k!   (rational)
```

This is the n-th coefficient of `EGF(labelSet)` times `n!` — where `EGF(labelSet) = exp(B.egf)`.

## Required code

```lean
/-- Labelled SET coefficient (rational): unordered count of partitioned labelled
    objects of size n drawn from B (with B.count 0 = 0). -/
noncomputable def labelSetCount (B : CombinatorialClass) (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1), ((labelPow B k).count n : ℚ) / k.factorial

/-- Identity: labelSet count divided by n! equals the n-th coefficient of
    `∑_{k=0}^{n} B.egf^k / k!`. This is the labelled SET → exp identity in coefficient form. -/
theorem labelSetCount_div_factorial_eq_partial_exp_coeff
    (B : CombinatorialClass) (n : ℕ) :
    labelSetCount B n / n.factorial =
      ∑ k ∈ Finset.range (n + 1), coeff n ((B.egf : PowerSeries ℚ) ^ k) / k.factorial := by
  sorry  -- per-k: ((labelPow B k).count n / k!) / n! = coeff n (B.egf^k) / k!
         -- via labelPow_egf and coeff_egf
```

## Recipe

```lean
unfold labelSetCount
rw [Finset.sum_div]   -- distribute the / n! across the sum
apply Finset.sum_congr rfl
intro k _
-- Goal: ((labelPow B k).count n / k!) / n! = coeff n (B.egf^k) / k!
-- Note: coeff n (B.egf^k) = coeff n (labelPow B k).egf = (labelPow B k).count n / n!
-- So RHS = ((labelPow B k).count n / n!) / k!
-- LHS  = ((labelPow B k).count n / k!) / n!
-- Both equal (labelPow B k).count n / (k! * n!) by field rearrangement.
rw [← labelPow_egf, coeff_egf]
field_simp
ring
```

(Adapt as needed — `Finset.sum_div` may not exist for ℚ in this form; use `div_eq_mul_inv` + `Finset.sum_mul` instead.)

## Bonus (if cheap)

If Mathlib has a way to express `exp(B.egf)` for `B.egf` with zero constant term — e.g. via `PowerSeries.exp_comp` or a substitution lemma — link `labelSetCount n / n!` to `coeff n (exp(B.egf))`. Otherwise leave the partial sum form.

## Hard constraints

- `lake build` green; current 2764 jobs.
- No new sorrys when delivered.
- Two real attempts; if blocked file `HANDOFF/outbox/task-labelset-reply.md`.

## Reply format

`HANDOFF/outbox/task-labelset-reply.md` with diff summary + `Codex: idle — task done`.
