# Task — `atomOfSize n` primitive

**File:** `AnalyticCombinatorics/PartA/Ch1/CombinatorialClass.lean` (append, near the existing `Atom` and `Epsilon` definitions)

**Goal:** Generalize `Atom` and `Epsilon` into `atomOfSize n` — a class with one object of size n. Prove its count formula and its OGF closed form.

```lean
/-- A single object of size n (`atomOfSize 0 = Epsilon`, `atomOfSize 1 = Atom`). -/
def atomOfSize (n : ℕ) : CombinatorialClass where
  Obj := Unit
  size _ := n
  finite_level _ := Set.finite_univ.subset (Set.subset_univ _)

/-- count formula: 1 if k = n else 0. -/
theorem atomOfSize_count (n k : ℕ) :
    (atomOfSize n).count k = if k = n then 1 else 0 := by
  sorry  -- pattern from Atom_ogf / Epsilon_ogf existing proofs

/-- OGF: atomOfSize n has OGF X^n. -/
theorem atomOfSize_ogf (n : ℕ) : (atomOfSize n).ogf = PowerSeries.X ^ n := by
  sorry  -- ext m; rw [coeff_ogf, atomOfSize_count, PowerSeries.coeff_X_pow]
         -- both sides are δ_{m, n}.
```

## Hint

Mathlib has `PowerSeries.coeff_X_pow : coeff k (X^n) = if k = n then 1 else 0`. This makes the OGF proof a one-liner once `atomOfSize_count` is in.

The count proof can mirror `Atom_ogf` from earlier in the file: Unique instance, by_cases on equality, level cardinality 1 vs 0.

## Hard constraints

- Build green
- No new sorrys when delivered
- Write the reply file at HANDOFF/outbox/task-atom-of-size-reply.md
