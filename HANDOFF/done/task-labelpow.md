# Task — `labelPow` (k-fold labelled product) and EGF identity

**File:** `AnalyticCombinatorics/PartA/Ch2/LabelledClass.lean` (append)

**Goal:** Define the k-fold labelled product `labelPow A k` and prove its EGF is `A.egf^k`.

## Required code

```lean
/-- k-fold labelled product of A with itself. By convention `labelPow A 0 = Epsilon`
    (the labelled-product unit) and `labelPow A (k+1) = A.labelProd (labelPow A k)`. -/
noncomputable def labelPow : CombinatorialClass → ℕ → CombinatorialClass
  | _, 0     => Epsilon
  | A, k + 1 => A.labelProd (labelPow A k)

/-- The EGF of `labelPow A k` is `A.egf ^ k`. -/
theorem labelPow_egf (A : CombinatorialClass) (k : ℕ) :
    (labelPow A k).egf = A.egf ^ k := by
  sorry  -- induction on k, using:
         --   labelPow A 0 = Epsilon, Epsilon.egf = 1,        and pow_zero
         --   labelPow A (k+1) = A.labelProd (labelPow A k),  and labelProd_egf

/-- The EGF coefficient of `labelPow A k` at `n` divided by `n!` matches
    the n-th coefficient of `A.egf ^ k`. -/
theorem labelPow_count_div_factorial_eq_coeff_pow (A : CombinatorialClass) (k n : ℕ) :
    ((labelPow A k).count n : ℚ) / n.factorial = coeff n (A.egf ^ k) := by
  rw [← coeff_egf, labelPow_egf]
```

## Need first: `Epsilon.egf = 1`

This is the labelled analogue of `Epsilon_ogf` (which we already have at the OGF level).

```lean
theorem Epsilon_egf : Epsilon.egf = 1 := by
  ext n
  rw [coeff_egf]
  -- (Epsilon.count n : ℚ) / n! = (1 : PowerSeries ℚ).coeff n
  rw [coeff_one]
  by_cases h : n = 0
  · subst h; rw [Epsilon_count_zero]; simp
  · rw [Epsilon_count_pos (Nat.pos_of_ne_zero h)]; simp [h]
```

(Already available helpers: `Epsilon_count_zero`, `Epsilon_count_pos`. The proof above is approximate — pick the cleanest form.)

## Already available (use freely)

- `Epsilon_count_zero : Epsilon.count 0 = 1`
- `Epsilon_count_pos : 0 < k → Epsilon.count k = 0`
- `labelProd : CombinatorialClass → CombinatorialClass → CombinatorialClass`
- `labelProd_egf : (A.labelProd B).egf = A.egf * B.egf`
- `coeff_egf : coeff n A.egf = (A.count n : ℚ) / n.factorial`

## Hard constraints

- `lake build` green; current 2764 jobs.
- No new sorrys when delivered.
- Two real attempts; if blocked file `HANDOFF/outbox/task-labelpow-reply.md` documenting the failure.

## Reply format

`HANDOFF/outbox/task-labelpow-reply.md` with diff summary + `Codex: idle — task done`.
