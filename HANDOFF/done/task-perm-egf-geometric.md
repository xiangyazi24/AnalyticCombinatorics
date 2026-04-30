# Task — `permClass_egf_mul_one_sub_X`

**File:** `AnalyticCombinatorics/PartA/Ch2/LabelledClass.lean` (append after `permClass_egf_coeff`)

**Goal:** Prove the geometric series identity for the permutation class:

```lean
theorem permClass_egf_mul_one_sub_X :
    permClass.egf * (1 - PowerSeries.X) = 1
```

i.e. `(1 + z + z² + ⋯) · (1 - z) = 1` over ℚ[[z]], specialized to permClass's EGF.

## What's already proven (use these)

- `permClass_egf_coeff (n : ℕ) : coeff n permClass.egf = 1` — every coefficient of the perm EGF is 1.
- `PowerSeries.coeff_mul`: coefficient of a product is the antidiagonal sum.
- `PowerSeries.coeff_one`: 1's coefficient is 1 at 0, 0 else.
- `PowerSeries.coeff_X`: X's coefficient is 1 at 1, 0 else.
- `Finset.Nat.sum_antidiagonal_eq_sum_range_succ` for converting antidiagonal sums.

## Recipe sketch

```
ext n
rw [coeff_mul, coeff_one]
rcases n with _ | m
· -- coeff 0 case: only (0, 0) contributes
  simp [permClass_egf_coeff, coeff_X]
· -- coeff (m+1) case:
  -- ∑_{p+q=m+1} 1 * coeff q (1 - X) = coeff(m+1) (...) - coeff(m) (...)
  -- = 1 - 1 = 0 = coeff (m+1) 1
  -- Strategy: show all but two summands vanish (q=0 contributes 1, q=1 contributes -1)
```

Mathlib's `coeff_one_sub_X` may help: `[zⁿ] (1 - X) = if n=0 then 1 else if n=1 then -1 else 0`.

If Mathlib doesn't have that compact form, prove it inline:
```
have hcoeff : ∀ k : ℕ, coeff k ((1 - PowerSeries.X) : PowerSeries ℚ) =
    if k = 0 then 1 else if k = 1 then (-1 : ℚ) else 0 := ...
```

## Hard constraints

- `lake build` green
- No new sorrys
- Two attempts then blocker (don't loop on simp/rw failures)

## Acceptance

Reply at `HANDOFF/outbox/task-perm-egf-geometric-reply.md` with diff summary + `Codex: idle — task done`.
