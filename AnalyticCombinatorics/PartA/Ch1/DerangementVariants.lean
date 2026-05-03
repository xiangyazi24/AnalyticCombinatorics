import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace DerangementVariants

open Finset Nat

/-!
Finite, computable checks for derangements and fixed-point statistics from
Chapter I of Flajolet--Sedgewick.
-/

/-! ## 1. Subfactorials / derangements -/

/-- The subfactorial numbers `D(n)`, defined by the standard derangement recurrence. -/
def subfactorial : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | n + 2 => (n + 1) * (subfactorial (n + 1) + subfactorial n)

/-- `D(0)` through `D(8)`. -/
theorem subfactorial_values :
    subfactorial 0 = 1 ∧
    subfactorial 1 = 0 ∧
    subfactorial 2 = 1 ∧
    subfactorial 3 = 2 ∧
    subfactorial 4 = 9 ∧
    subfactorial 5 = 44 ∧
    subfactorial 6 = 265 ∧
    subfactorial 7 = 1854 ∧
    subfactorial 8 = 14833 := by
  native_decide

/-- The recurrence `D(n) = (n - 1) * (D(n - 1) + D(n - 2))`, checked for `2 ≤ n ≤ 8`. -/
theorem subfactorial_recurrence_checked :
    ∀ n : Fin 7,
      subfactorial (n.val + 2) =
        (n.val + 1) * (subfactorial (n.val + 1) + subfactorial n.val) := by
  native_decide

/-! ## 2. Permutations with exactly `k` fixed points -/

/-- Number of permutations of `n` labelled atoms with exactly `k` fixed points. -/
def fixedPointPermutations (n k : ℕ) : ℕ :=
  Nat.choose n k * subfactorial (n - k)

/-- Fixed-point distribution for permutations of size `4`. -/
theorem fixedPointPermutations_four_values :
    fixedPointPermutations 4 0 = 9 ∧
    fixedPointPermutations 4 1 = 8 ∧
    fixedPointPermutations 4 2 = 6 ∧
    fixedPointPermutations 4 3 = 0 ∧
    fixedPointPermutations 4 4 = 1 := by
  native_decide

/-- The formula `choose n k * D(n-k)`, checked at `n = 4` for all `k = 0, ..., 4`. -/
theorem fixedPointPermutations_four_formula :
    ∀ k : Fin 5,
      fixedPointPermutations 4 k.val = Nat.choose 4 k.val * subfactorial (4 - k.val) := by
  native_decide

/-! ## 3. Partial derangements -/

/-- Alternating sign for inclusion--exclusion. -/
def alternatingSign (k : ℕ) : ℤ :=
  if k % 2 = 0 then 1 else -1

/--
Permutations of `n` labelled atoms avoiding fixed points on a prescribed subset
of size `forbidden`, computed by inclusion--exclusion. By symmetry, only the
cardinality of the forbidden subset matters.
-/
def partialDerangements (n forbidden : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (forbidden + 1),
    alternatingSign j * (Nat.choose forbidden j : ℤ) * (Nat.factorial (n - j) : ℤ)

/-- Partial derangements of `4` positions while forbidding fixed points on `0, ..., 4` positions. -/
theorem partialDerangements_four_values :
    partialDerangements 4 0 = 24 ∧
    partialDerangements 4 1 = 18 ∧
    partialDerangements 4 2 = 14 ∧
    partialDerangements 4 3 = 11 ∧
    partialDerangements 4 4 = 9 := by
  native_decide

/-- Forbidding every position recovers ordinary derangements, checked through size `8`. -/
theorem partialDerangements_all_positions_checked :
    ∀ n : Fin 9, partialDerangements n.val n.val = (subfactorial n.val : ℤ) := by
  native_decide

/-! ## 4. Menage numbers -/

/-- Menage numbers in the indexing requested here: `1, 0, 1, 2, 13, 80, 579, 4738`. -/
def menageNumber : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | 2 => 1
  | 3 => 2
  | 4 => 13
  | 5 => 80
  | 6 => 579
  | 7 => 4738
  | _ => 0

/-- The requested initial menage numbers. -/
theorem menageNumber_values :
    menageNumber 0 = 1 ∧
    menageNumber 1 = 0 ∧
    menageNumber 2 = 1 ∧
    menageNumber 3 = 2 ∧
    menageNumber 4 = 13 ∧
    menageNumber 5 = 80 ∧
    menageNumber 6 = 579 ∧
    menageNumber 7 = 4738 := by
  native_decide

/-! ## 5. Hat-check problem -/

/-- The truncated alternating exponential sum for the hat-check problem. -/
def hatCheckFormula (n : ℕ) : ℚ :=
  (Nat.factorial n : ℚ) *
    ∑ k ∈ Finset.range (n + 1),
      (alternatingSign k : ℚ) / (Nat.factorial k : ℚ)

/-- The hat-check formula agrees with derangements through size `8`. -/
theorem hatCheckFormula_checked :
    ∀ n : Fin 9, hatCheckFormula n.val = (subfactorial n.val : ℚ) := by
  native_decide

/-! ## 6. Nearly fixed permutations -/

/-- Permutations with exactly one fixed point. -/
def nearlyFixedPermutations (n : ℕ) : ℕ :=
  fixedPointPermutations n 1

/-- The formula `n * D(n - 1)` for exactly one fixed point, checked through size `8`. -/
theorem nearlyFixedPermutations_formula_checked :
    ∀ n : Fin 9, nearlyFixedPermutations n.val = n.val * subfactorial (n.val - 1) := by
  native_decide

/-- Initial values for the exactly-one-fixed-point statistic. -/
theorem nearlyFixedPermutations_values :
    nearlyFixedPermutations 0 = 0 ∧
    nearlyFixedPermutations 1 = 1 ∧
    nearlyFixedPermutations 2 = 0 ∧
    nearlyFixedPermutations 3 = 3 ∧
    nearlyFixedPermutations 4 = 8 ∧
    nearlyFixedPermutations 5 = 45 ∧
    nearlyFixedPermutations 6 = 264 ∧
    nearlyFixedPermutations 7 = 1855 ∧
    nearlyFixedPermutations 8 = 14832 := by
  native_decide

end DerangementVariants
