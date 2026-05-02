import Mathlib.Tactic
import AnalyticCombinatorics.PartA.Ch2.CycleIndex
import AnalyticCombinatorics.PartA.Ch2.Derangements

open Finset

set_option linter.style.nativeDecide false

/-!
Chapter II exponential formula checks.

This file records the coefficient-level form of the labelled identity

  PERM = SET(CYC(Atom)).

For permutations, the EGF is `1 / (1 - z)`, so every ordinary coefficient of
the EGF is `1`.  The connected components are cycles; their EGF coefficient is
`1 / n` in positive degree.  We compute the finite coefficient of
`exp(∑_{n≥1} z^n/n)` by summing the powers of the cycle coefficient stream.
-/

/-- Number of permutations on an `n`-element labelled set. -/
def permCount (n : ℕ) : ℕ :=
  n.factorial

/-- Number of connected permutation components, i.e. cycles, on `n` labels. -/
def connectedPermCount (n : ℕ) : ℕ :=
  if n = 0 then 0 else (n - 1).factorial

theorem permCount_eq_factorial (n : ℕ) : permCount n = n.factorial := by
  rfl

theorem connectedPermCount_zero : connectedPermCount 0 = 0 := by
  rfl

theorem connectedPermCount_pos {n : ℕ} (hn : 0 < n) :
    connectedPermCount n = (n - 1).factorial := by
  simp [connectedPermCount, Nat.ne_of_gt hn]

/-- Checked count-level cycle decomposition:
permutations are sets of cycles, grouped by the number of cycles. -/
theorem permCount_eq_cycleType_row_sum_checked (n : ℕ) (hn : n ≤ 8) :
    permCount n = ∑ k ∈ Finset.range (n + 1), cycleTypeCount n k := by
  rw [permCount_eq_factorial, stirling1_row_sum_checked n hn]

/-! ## Computable EGF coefficients for `SET(CYC(Atom))` -/

/-- Cauchy product for coefficient streams. -/
def egfMulCoeff (a b : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1), a k * b (n - k)

/-- Coefficient stream for powers of an EGF. -/
def egfPowCoeff (a : ℕ → ℚ) : ℕ → ℕ → ℚ
  | 0, n => if n = 0 then 1 else 0
  | k + 1, n => egfMulCoeff a (egfPowCoeff a k) n

/-- EGF coefficient of the cycle component class `CYC(Atom)`.

At positive size `n`, there are `(n-1)!` cycles, hence EGF coefficient
`(n-1)! / n! = 1/n`. -/
def cycleComponentEgfCoeff (n : ℕ) : ℚ :=
  if n = 0 then 0 else (1 : ℚ) / n

theorem cycleComponentEgfCoeff_eq_connected_div_factorial (n : ℕ) :
    cycleComponentEgfCoeff n = (connectedPermCount n : ℚ) / n.factorial := by
  cases n with
  | zero =>
      native_decide
  | succ n =>
      rw [cycleComponentEgfCoeff, connectedPermCount_pos (Nat.succ_pos n)]
      simp only [Nat.succ_ne_zero, ↓reduceIte]
      simp only [Nat.succ_sub_one]
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add_one]
      field_simp [Nat.cast_ne_zero.mpr n.factorial_pos.ne',
        show ((n : ℚ) + 1) ≠ 0 by positivity]

/-- Coefficient of `SET(CYC(Atom)) = exp(CYC(Atom))`, computed finitely in
degree `n`.  Terms with more than `n` components cannot contribute, so the
finite sum through `n` suffices. -/
def setCyclePermEgfCoeff (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1), egfPowCoeff cycleComponentEgfCoeff k n / k.factorial

/-- Count-level version of `SET(CYC(Atom))`, obtained by multiplying the EGF
coefficient by `n!`. -/
def setCyclePermCount (n : ℕ) : ℚ :=
  (n.factorial : ℚ) * setCyclePermEgfCoeff n

/-- Coefficient-level verification of
`exp(log(1/(1-z))) = 1/(1-z)` for `n = 0, ..., 8`. -/
theorem setCyclePermEgfCoeff_checked (n : ℕ) (hn : n ≤ 8) :
    setCyclePermEgfCoeff n = 1 := by
  interval_cases n <;> native_decide

/-- Count-level verification of `PERM = SET(CYC(Atom))` for `n = 0, ..., 8`. -/
theorem permCount_eq_setCyclePermCount_checked (n : ℕ) (hn : n ≤ 8) :
    (permCount n : ℚ) = setCyclePermCount n := by
  rw [permCount_eq_factorial, setCyclePermCount, setCyclePermEgfCoeff_checked n hn]
  simp

example : setCyclePermEgfCoeff 0 = 1 := by native_decide
example : setCyclePermEgfCoeff 1 = 1 := by native_decide
example : setCyclePermEgfCoeff 2 = 1 := by native_decide
example : setCyclePermEgfCoeff 3 = 1 := by native_decide
example : setCyclePermEgfCoeff 4 = 1 := by native_decide
example : setCyclePermEgfCoeff 5 = 1 := by native_decide
example : setCyclePermEgfCoeff 6 = 1 := by native_decide
example : setCyclePermEgfCoeff 7 = 1 := by native_decide
example : setCyclePermEgfCoeff 8 = 1 := by native_decide
