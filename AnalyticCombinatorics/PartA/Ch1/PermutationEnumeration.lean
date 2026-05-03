import Mathlib.Tactic

set_option linter.style.nativeDecide false

open Finset Nat

namespace PermutationEnumeration

/-!
Chapter I/II finite checks for permutation counting and enumeration.

Topics covered:
  1. Factorial basics
  2. Permutations by number of fixed points (inclusion-exclusion)
  3. Subfactorial / derangement recurrence
  4. 321-avoiding permutations and Catalan numbers
  5. Involutions (self-inverse permutations)
  6. Double factorial and perfect matchings
-/

/-! ## 1. Factorial basics -/

/-- Factorials 0! through 10!. -/
theorem factorial_values :
    Nat.factorial 0  = 1       ∧
    Nat.factorial 1  = 1       ∧
    Nat.factorial 2  = 2       ∧
    Nat.factorial 3  = 6       ∧
    Nat.factorial 4  = 24      ∧
    Nat.factorial 5  = 120     ∧
    Nat.factorial 6  = 720     ∧
    Nat.factorial 7  = 5040    ∧
    Nat.factorial 8  = 40320   ∧
    Nat.factorial 9  = 362880  ∧
    Nat.factorial 10 = 3628800 := by
  native_decide

/-- Recurrence (n+1)! = (n+1) * n!, checked for n = 0..9. -/
theorem factorial_recurrence :
    Nat.factorial 1  = 1  * Nat.factorial 0  ∧
    Nat.factorial 2  = 2  * Nat.factorial 1  ∧
    Nat.factorial 3  = 3  * Nat.factorial 2  ∧
    Nat.factorial 4  = 4  * Nat.factorial 3  ∧
    Nat.factorial 5  = 5  * Nat.factorial 4  ∧
    Nat.factorial 6  = 6  * Nat.factorial 5  ∧
    Nat.factorial 7  = 7  * Nat.factorial 6  ∧
    Nat.factorial 8  = 8  * Nat.factorial 7  ∧
    Nat.factorial 9  = 9  * Nat.factorial 8  ∧
    Nat.factorial 10 = 10 * Nat.factorial 9  := by
  native_decide

/-- n! divides (2n)! for n = 1..8. -/
theorem factorial_divides_double_1 : Nat.factorial 1 ∣ Nat.factorial (2 * 1) := by native_decide
theorem factorial_divides_double_2 : Nat.factorial 2 ∣ Nat.factorial (2 * 2) := by native_decide
theorem factorial_divides_double_3 : Nat.factorial 3 ∣ Nat.factorial (2 * 3) := by native_decide
theorem factorial_divides_double_4 : Nat.factorial 4 ∣ Nat.factorial (2 * 4) := by native_decide
theorem factorial_divides_double_5 : Nat.factorial 5 ∣ Nat.factorial (2 * 5) := by native_decide
theorem factorial_divides_double_6 : Nat.factorial 6 ∣ Nat.factorial (2 * 6) := by native_decide
theorem factorial_divides_double_7 : Nat.factorial 7 ∣ Nat.factorial (2 * 7) := by native_decide
theorem factorial_divides_double_8 : Nat.factorial 8 ∣ Nat.factorial (2 * 8) := by native_decide

/-! ## 2. Permutations by number of fixed points -/

/-- Derangement numbers D(0)..D(8):
    D(0) = 1 (empty permutation), D(1) = 0, D(2) = 1, D(3) = 2, D(4) = 9,
    D(5) = 44, D(6) = 265, D(7) = 1854, D(8) = 14833. -/
def derangementTab : Fin 9 → ℕ := ![1, 0, 1, 2, 9, 44, 265, 1854, 14833]

/-- Inclusion-exclusion identity:
    Σ_{k=0}^{n} C(n,k) * D(n-k) = n!
    checked for n = 3, 4, 5, 6, 7. -/
theorem ie_identity_3 :
    Nat.choose 3 0 * derangementTab ⟨3, by norm_num⟩ +
    Nat.choose 3 1 * derangementTab ⟨2, by norm_num⟩ +
    Nat.choose 3 2 * derangementTab ⟨1, by norm_num⟩ +
    Nat.choose 3 3 * derangementTab ⟨0, by norm_num⟩ =
    Nat.factorial 3 := by native_decide

theorem ie_identity_4 :
    Nat.choose 4 0 * derangementTab ⟨4, by norm_num⟩ +
    Nat.choose 4 1 * derangementTab ⟨3, by norm_num⟩ +
    Nat.choose 4 2 * derangementTab ⟨2, by norm_num⟩ +
    Nat.choose 4 3 * derangementTab ⟨1, by norm_num⟩ +
    Nat.choose 4 4 * derangementTab ⟨0, by norm_num⟩ =
    Nat.factorial 4 := by native_decide

theorem ie_identity_5 :
    Nat.choose 5 0 * derangementTab ⟨5, by norm_num⟩ +
    Nat.choose 5 1 * derangementTab ⟨4, by norm_num⟩ +
    Nat.choose 5 2 * derangementTab ⟨3, by norm_num⟩ +
    Nat.choose 5 3 * derangementTab ⟨2, by norm_num⟩ +
    Nat.choose 5 4 * derangementTab ⟨1, by norm_num⟩ +
    Nat.choose 5 5 * derangementTab ⟨0, by norm_num⟩ =
    Nat.factorial 5 := by native_decide

theorem ie_identity_6 :
    Nat.choose 6 0 * derangementTab ⟨6, by norm_num⟩ +
    Nat.choose 6 1 * derangementTab ⟨5, by norm_num⟩ +
    Nat.choose 6 2 * derangementTab ⟨4, by norm_num⟩ +
    Nat.choose 6 3 * derangementTab ⟨3, by norm_num⟩ +
    Nat.choose 6 4 * derangementTab ⟨2, by norm_num⟩ +
    Nat.choose 6 5 * derangementTab ⟨1, by norm_num⟩ +
    Nat.choose 6 6 * derangementTab ⟨0, by norm_num⟩ =
    Nat.factorial 6 := by native_decide

theorem ie_identity_7 :
    Nat.choose 7 0 * derangementTab ⟨7, by norm_num⟩ +
    Nat.choose 7 1 * derangementTab ⟨6, by norm_num⟩ +
    Nat.choose 7 2 * derangementTab ⟨5, by norm_num⟩ +
    Nat.choose 7 3 * derangementTab ⟨4, by norm_num⟩ +
    Nat.choose 7 4 * derangementTab ⟨3, by norm_num⟩ +
    Nat.choose 7 5 * derangementTab ⟨2, by norm_num⟩ +
    Nat.choose 7 6 * derangementTab ⟨1, by norm_num⟩ +
    Nat.choose 7 7 * derangementTab ⟨0, by norm_num⟩ =
    Nat.factorial 7 := by native_decide

/-! ## 3. Derangement recurrence -/

/-- D(n+2) = (n+1)*(D(n+1) + D(n)), verified for n = 0..6. -/
theorem derangement_rec_0 :
    derangementTab ⟨2, by norm_num⟩ =
      1 * (derangementTab ⟨1, by norm_num⟩ + derangementTab ⟨0, by norm_num⟩) := by native_decide

theorem derangement_rec_1 :
    derangementTab ⟨3, by norm_num⟩ =
      2 * (derangementTab ⟨2, by norm_num⟩ + derangementTab ⟨1, by norm_num⟩) := by native_decide

theorem derangement_rec_2 :
    derangementTab ⟨4, by norm_num⟩ =
      3 * (derangementTab ⟨3, by norm_num⟩ + derangementTab ⟨2, by norm_num⟩) := by native_decide

theorem derangement_rec_3 :
    derangementTab ⟨5, by norm_num⟩ =
      4 * (derangementTab ⟨4, by norm_num⟩ + derangementTab ⟨3, by norm_num⟩) := by native_decide

theorem derangement_rec_4 :
    derangementTab ⟨6, by norm_num⟩ =
      5 * (derangementTab ⟨5, by norm_num⟩ + derangementTab ⟨4, by norm_num⟩) := by native_decide

theorem derangement_rec_5 :
    derangementTab ⟨7, by norm_num⟩ =
      6 * (derangementTab ⟨6, by norm_num⟩ + derangementTab ⟨5, by norm_num⟩) := by native_decide

theorem derangement_rec_6 :
    derangementTab ⟨8, by norm_num⟩ =
      7 * (derangementTab ⟨7, by norm_num⟩ + derangementTab ⟨6, by norm_num⟩) := by native_decide

/-! ## 4. 321-avoiding permutations and Catalan numbers -/

/-- Catalan numbers C_0..C_8. -/
def catalanSeq : Fin 9 → ℕ := ![1, 1, 2, 5, 14, 42, 132, 429, 1430]

/-- C_n = C(2n, n) / (n+1) for n = 0..8. -/
theorem catalan_formula_0 :
    catalanSeq ⟨0, by norm_num⟩ = Nat.choose (2 * 0) 0 / (0 + 1) := by native_decide
theorem catalan_formula_1 :
    catalanSeq ⟨1, by norm_num⟩ = Nat.choose (2 * 1) 1 / (1 + 1) := by native_decide
theorem catalan_formula_2 :
    catalanSeq ⟨2, by norm_num⟩ = Nat.choose (2 * 2) 2 / (2 + 1) := by native_decide
theorem catalan_formula_3 :
    catalanSeq ⟨3, by norm_num⟩ = Nat.choose (2 * 3) 3 / (3 + 1) := by native_decide
theorem catalan_formula_4 :
    catalanSeq ⟨4, by norm_num⟩ = Nat.choose (2 * 4) 4 / (4 + 1) := by native_decide
theorem catalan_formula_5 :
    catalanSeq ⟨5, by norm_num⟩ = Nat.choose (2 * 5) 5 / (5 + 1) := by native_decide
theorem catalan_formula_6 :
    catalanSeq ⟨6, by norm_num⟩ = Nat.choose (2 * 6) 6 / (6 + 1) := by native_decide
theorem catalan_formula_7 :
    catalanSeq ⟨7, by norm_num⟩ = Nat.choose (2 * 7) 7 / (7 + 1) := by native_decide
theorem catalan_formula_8 :
    catalanSeq ⟨8, by norm_num⟩ = Nat.choose (2 * 8) 8 / (8 + 1) := by native_decide

/-- C_n < n! for n = 4..8. -/
theorem catalan_lt_factorial_4 : catalanSeq ⟨4, by norm_num⟩ < Nat.factorial 4 := by native_decide
theorem catalan_lt_factorial_5 : catalanSeq ⟨5, by norm_num⟩ < Nat.factorial 5 := by native_decide
theorem catalan_lt_factorial_6 : catalanSeq ⟨6, by norm_num⟩ < Nat.factorial 6 := by native_decide
theorem catalan_lt_factorial_7 : catalanSeq ⟨7, by norm_num⟩ < Nat.factorial 7 := by native_decide
theorem catalan_lt_factorial_8 : catalanSeq ⟨8, by norm_num⟩ < Nat.factorial 8 := by native_decide

/-! ## 5. Involutions -/

/-- Involution counts a(0)..a(9):
    a(n) = number of self-inverse permutations of [n]. -/
def involutionTab : Fin 10 → ℕ := ![1, 1, 2, 4, 10, 26, 76, 232, 764, 2620]

/-- a(n+2) = a(n+1) + (n+1)*a(n), verified for n = 0..7. -/
theorem involution_rec_0 :
    involutionTab ⟨2, by norm_num⟩ =
      involutionTab ⟨1, by norm_num⟩ + 1 * involutionTab ⟨0, by norm_num⟩ := by native_decide

theorem involution_rec_1 :
    involutionTab ⟨3, by norm_num⟩ =
      involutionTab ⟨2, by norm_num⟩ + 2 * involutionTab ⟨1, by norm_num⟩ := by native_decide

theorem involution_rec_2 :
    involutionTab ⟨4, by norm_num⟩ =
      involutionTab ⟨3, by norm_num⟩ + 3 * involutionTab ⟨2, by norm_num⟩ := by native_decide

theorem involution_rec_3 :
    involutionTab ⟨5, by norm_num⟩ =
      involutionTab ⟨4, by norm_num⟩ + 4 * involutionTab ⟨3, by norm_num⟩ := by native_decide

theorem involution_rec_4 :
    involutionTab ⟨6, by norm_num⟩ =
      involutionTab ⟨5, by norm_num⟩ + 5 * involutionTab ⟨4, by norm_num⟩ := by native_decide

theorem involution_rec_5 :
    involutionTab ⟨7, by norm_num⟩ =
      involutionTab ⟨6, by norm_num⟩ + 6 * involutionTab ⟨5, by norm_num⟩ := by native_decide

theorem involution_rec_6 :
    involutionTab ⟨8, by norm_num⟩ =
      involutionTab ⟨7, by norm_num⟩ + 7 * involutionTab ⟨6, by norm_num⟩ := by native_decide

theorem involution_rec_7 :
    involutionTab ⟨9, by norm_num⟩ =
      involutionTab ⟨8, by norm_num⟩ + 8 * involutionTab ⟨7, by norm_num⟩ := by native_decide

/-! ## 6. Double factorial and perfect matchings -/

/-- (2k-1)!! for k = 0..7:
    Entry n is (2n-1)!! = number of perfect matchings on 2n elements.
    Convention: (2*0-1)!! = 1 (empty product). -/
def doubleFactorial : Fin 8 → ℕ := ![1, 1, 3, 15, 105, 945, 10395, 135135]

/-- Recurrence df(n+1) = (2*n+1) * df(n), verified for n = 0..6. -/
theorem doubleFactorial_rec_0 :
    doubleFactorial ⟨1, by norm_num⟩ =
      (2 * 0 + 1) * doubleFactorial ⟨0, by norm_num⟩ := by native_decide

theorem doubleFactorial_rec_1 :
    doubleFactorial ⟨2, by norm_num⟩ =
      (2 * 1 + 1) * doubleFactorial ⟨1, by norm_num⟩ := by native_decide

theorem doubleFactorial_rec_2 :
    doubleFactorial ⟨3, by norm_num⟩ =
      (2 * 2 + 1) * doubleFactorial ⟨2, by norm_num⟩ := by native_decide

theorem doubleFactorial_rec_3 :
    doubleFactorial ⟨4, by norm_num⟩ =
      (2 * 3 + 1) * doubleFactorial ⟨3, by norm_num⟩ := by native_decide

theorem doubleFactorial_rec_4 :
    doubleFactorial ⟨5, by norm_num⟩ =
      (2 * 4 + 1) * doubleFactorial ⟨4, by norm_num⟩ := by native_decide

theorem doubleFactorial_rec_5 :
    doubleFactorial ⟨6, by norm_num⟩ =
      (2 * 5 + 1) * doubleFactorial ⟨5, by norm_num⟩ := by native_decide

theorem doubleFactorial_rec_6 :
    doubleFactorial ⟨7, by norm_num⟩ =
      (2 * 6 + 1) * doubleFactorial ⟨6, by norm_num⟩ := by native_decide

/-- Identity: df(n) * 2^n * n! = (2n)!, verified for n = 1..6. -/
theorem doubleFactorial_identity_1 :
    doubleFactorial ⟨1, by norm_num⟩ * 2 ^ 1 * Nat.factorial 1 =
      Nat.factorial (2 * 1) := by native_decide

theorem doubleFactorial_identity_2 :
    doubleFactorial ⟨2, by norm_num⟩ * 2 ^ 2 * Nat.factorial 2 =
      Nat.factorial (2 * 2) := by native_decide

theorem doubleFactorial_identity_3 :
    doubleFactorial ⟨3, by norm_num⟩ * 2 ^ 3 * Nat.factorial 3 =
      Nat.factorial (2 * 3) := by native_decide

theorem doubleFactorial_identity_4 :
    doubleFactorial ⟨4, by norm_num⟩ * 2 ^ 4 * Nat.factorial 4 =
      Nat.factorial (2 * 4) := by native_decide

theorem doubleFactorial_identity_5 :
    doubleFactorial ⟨5, by norm_num⟩ * 2 ^ 5 * Nat.factorial 5 =
      Nat.factorial (2 * 5) := by native_decide

theorem doubleFactorial_identity_6 :
    doubleFactorial ⟨6, by norm_num⟩ * 2 ^ 6 * Nat.factorial 6 =
      Nat.factorial (2 * 6) := by native_decide

end PermutationEnumeration
