import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Exp
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass
import AnalyticCombinatorics.PartA.Ch2.LabelledClass

set_option linter.style.show false
set_option linter.style.nativeDecide false

open PowerSeries

namespace CombinatorialClass

/-!
Chapter II labelled SET and CYCLE sanity checks.

`LabelledClass` contains the finite coefficient forms for labelled SET and
CYCLE.  This file records concrete coefficient/count verifications for atoms,
cycles, permutations, and involutions.
-/

/-! ## SET of atoms -/

/-- SET(Atom) has one object on each label set. -/
theorem labelSetCount_Atom_all_subsets (n : ℕ) :
    labelSetCount Atom n = 1 :=
  labelSetCount_Atom n

/-- A two-coloured atom class.  SET(TwoAtom) chooses one of two colours for
each label, hence has `2^n` labelled structures of size `n`. -/
noncomputable abbrev TwoAtom : CombinatorialClass :=
  Atom.disjSum Atom

/-- The EGF of `TwoAtom` is `2z`. -/
theorem TwoAtom_egf : TwoAtom.egf = (2 : PowerSeries ℚ) * PowerSeries.X := by
  rw [TwoAtom, disjSum_egf, Atom_egf]
  ring

private lemma coeff_two_mul_X_pow (k n : ℕ) :
    coeff n (((2 : PowerSeries ℚ) * PowerSeries.X) ^ k) =
      if n = k then (2 : ℚ) ^ k else 0 := by
  rw [mul_pow]
  have hC : ((2 : PowerSeries ℚ) ^ k) = PowerSeries.C ((2 : ℚ) ^ k) := by
    change ((PowerSeries.C (2 : ℚ)) ^ k) = PowerSeries.C ((2 : ℚ) ^ k)
    simp
  rw [hC, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
  split_ifs <;> simp

/-- Iterated labelled product of two-coloured atoms. -/
theorem labelPow_TwoAtom_count (k n : ℕ) :
    (labelPow TwoAtom k).count n = if n = k then n.factorial * 2 ^ n else 0 := by
  have hcoeff := labelPow_count_div_factorial_eq_coeff_pow TwoAtom k n
  rw [TwoAtom_egf, coeff_two_mul_X_pow] at hcoeff
  by_cases hnk : n = k
  · subst n
    simp only [if_true] at hcoeff ⊢
    field_simp [Nat.cast_ne_zero.mpr k.factorial_pos.ne'] at hcoeff
    exact_mod_cast hcoeff
  · simp only [if_false, hnk] at hcoeff ⊢
    field_simp [Nat.cast_ne_zero.mpr n.factorial_pos.ne'] at hcoeff
    rw [mul_zero] at hcoeff
    exact Nat.cast_eq_zero.mp hcoeff

/-- SET(TwoAtom) has count `2^n`; equivalently its EGF coefficient is
`2^n / n!`, the coefficient of `exp(2z)`. -/
theorem labelSetCount_TwoAtom (n : ℕ) :
    labelSetCount TwoAtom n = (2 ^ n : ℚ) := by
  rw [labelSetCount]
  rw [Finset.sum_eq_single n]
  · rw [labelPow_TwoAtom_count n n, if_pos rfl]
    rw [Nat.cast_mul]
    field_simp [Nat.cast_ne_zero.mpr n.factorial_pos.ne']
    norm_num
  · intro k _ hkn
    rw [labelPow_TwoAtom_count k n, if_neg (Ne.symm hkn)]
    simp
  · intro hn
    exfalso
    exact hn (Finset.mem_range.mpr (Nat.lt_succ_self n))

theorem labelSetCount_TwoAtom_coeff (n : ℕ) :
    labelSetCount TwoAtom n / n.factorial = (2 ^ n : ℚ) / n.factorial := by
  rw [labelSetCount_TwoAtom]

/-! ## CYCLE of atoms -/

/-- CYCLE(Atom) counts cyclic permutations: `(n-1)!` for positive size `n`. -/
theorem labelCycCount_Atom_pos {n : ℕ} (hn : 0 < n) :
    labelCycCount Atom n = ((n - 1).factorial : ℚ) := by
  cases n with
  | zero => omega
  | succ n =>
      simpa using labelCycCount_Atom_succ n

example : labelCycCount Atom 1 = 1 := by
  rw [labelCycCount_Atom_succ]
  norm_num [Nat.factorial]

example : labelCycCount Atom 2 = 1 := by
  rw [labelCycCount_Atom_succ]
  norm_num [Nat.factorial]

example : labelCycCount Atom 3 = 2 := by
  rw [labelCycCount_Atom_succ]
  norm_num [Nat.factorial]

example : labelCycCount Atom 4 = 6 := by
  rw [labelCycCount_Atom_succ]
  norm_num [Nat.factorial]

example : labelCycCount Atom 5 = 24 := by
  rw [labelCycCount_Atom_succ]
  norm_num [Nat.factorial]

/-! ## PERM = SET(CYCLE(Atom)), checked at small coefficients -/

/-- Cauchy-product coefficient for computable coefficient streams. -/
def mulCoeff (a b : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ p ∈ Finset.antidiagonal n, a p.1 * b p.2

/-- Coefficient of the `k`-th power of a computable coefficient stream. -/
def powCoeff (a : ℕ → ℚ) : ℕ → ℕ → ℚ
  | 0, n => if n = 0 then 1 else 0
  | k + 1, n => mulCoeff a (powCoeff a k) n

/-- Coefficients of `log (1 / (1 - z))`, i.e. CYCLE(Atom). -/
def cycleAtomCoeff (n : ℕ) : ℚ :=
  if n = 0 then 0 else (1 : ℚ) / n

/-- The computable coefficient stream agrees with `labelCycCount Atom / n!`. -/
theorem cycleAtomCoeff_eq_labelCycCount_div_factorial (n : ℕ) :
    cycleAtomCoeff n = labelCycCount Atom n / n.factorial := by
  cases n with
  | zero => simp [cycleAtomCoeff, labelCycCount]
  | succ n =>
      rw [cycleAtomCoeff, if_neg (Nat.succ_ne_zero n), labelCycCount_Atom_succ]
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add_one]
      field_simp [Nat.cast_ne_zero.mpr n.factorial_pos.ne',
        show ((n : ℚ) + 1) ≠ 0 by positivity]

/-- Coefficient of `exp(log(1/(1-z)))`, computed as finite SET coefficients. -/
def setCycleAtomCoeff (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1), powCoeff cycleAtomCoeff k n / k.factorial

/-- Count-level form: multiply the EGF coefficient by `n!`. -/
def permViaSetCycleCount (n : ℕ) : ℚ :=
  (n.factorial : ℚ) * setCycleAtomCoeff n

example : setCycleAtomCoeff 1 = 1 := by native_decide
example : setCycleAtomCoeff 2 = 1 := by native_decide
example : setCycleAtomCoeff 3 = 1 := by native_decide
example : setCycleAtomCoeff 4 = 1 := by native_decide
example : setCycleAtomCoeff 5 = 1 := by native_decide

example : permViaSetCycleCount 1 = (1 : ℚ) := by native_decide
example : permViaSetCycleCount 2 = (2 : ℚ) := by native_decide
example : permViaSetCycleCount 3 = (6 : ℚ) := by native_decide
example : permViaSetCycleCount 4 = (24 : ℚ) := by native_decide
example : permViaSetCycleCount 5 = (120 : ℚ) := by native_decide

/-! ## Involutions = SET of singleton and pair components -/

/-- Number of involutions on `n` labelled atoms.  The recurrence is the usual
choice: label `n` is fixed, or it is paired with one of the other `n-1` labels. -/
def involutionCount : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => involutionCount (n + 1) + (n + 1) * involutionCount n

theorem involutionCount_succ_succ (n : ℕ) :
    involutionCount (n + 2) =
      involutionCount (n + 1) + (n + 1) * involutionCount n := by
  rfl

example : involutionCount 0 = 1 := by native_decide
example : involutionCount 1 = 1 := by native_decide
example : involutionCount 2 = 2 := by native_decide
example : involutionCount 3 = 4 := by native_decide
example : involutionCount 4 = 10 := by native_decide
example : involutionCount 5 = 26 := by native_decide

/-- Coefficient formula for `exp(z + z^2/2) = exp z * exp(z^2/2)`. -/
def involutionEgfCoeff (n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (n / 2 + 1),
    if 2 * j ≤ n then
      (1 : ℚ) / ((n - 2 * j).factorial * j.factorial * 2 ^ j : ℕ)
    else 0

/-- The formal EGF named in the symbolic specification. -/
noncomputable def involutionEgf : PowerSeries ℚ :=
  (PowerSeries.exp ℚ).subst
    (PowerSeries.X + PowerSeries.C (1 / 2 : ℚ) * PowerSeries.X ^ 2)

example : involutionEgfCoeff 0 = (involutionCount 0 : ℚ) / (0 : ℕ).factorial := by
  native_decide

example : involutionEgfCoeff 1 = (involutionCount 1 : ℚ) / (1 : ℕ).factorial := by
  native_decide

example : involutionEgfCoeff 2 = (involutionCount 2 : ℚ) / (2 : ℕ).factorial := by
  native_decide

example : involutionEgfCoeff 3 = (involutionCount 3 : ℚ) / (3 : ℕ).factorial := by
  native_decide

example : involutionEgfCoeff 4 = (involutionCount 4 : ℚ) / (4 : ℕ).factorial := by
  native_decide

example : involutionEgfCoeff 5 = (involutionCount 5 : ℚ) / (5 : ℕ).factorial := by
  native_decide

end CombinatorialClass
