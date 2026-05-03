import Mathlib.Tactic
set_option linter.style.nativeDecide false

/-!
# Symmetric Functions: finite Chapter I checks

Small bounded computations for elementary symmetric functions, power sums,
monomial symmetric functions, Schur specializations, and hook-length counts.
-/

namespace SymmetricFunctions

/-! ## Elementary symmetric functions at all ones -/

/-- Values of `e_k(1, ..., 1)` for six variables, `k = 0, ..., 6`. -/
def elementaryOnes6 : Fin 7 → ℕ := ![1, 6, 15, 20, 15, 6, 1]

/-- Values of `e_k(1, ..., 1)` for eight variables, `k = 0, ..., 8`. -/
def elementaryOnes8 : Fin 9 → ℕ := ![1, 8, 28, 56, 70, 56, 28, 8, 1]

theorem elementaryOnes6_choose :
    ∀ k : Fin 7, elementaryOnes6 k = Nat.choose 6 k.val := by
  native_decide

theorem elementaryOnes8_choose :
    ∀ k : Fin 9, elementaryOnes8 k = Nat.choose 8 k.val := by
  native_decide

theorem elementaryOnes6_row_sum :
    elementaryOnes6 0 + elementaryOnes6 1 + elementaryOnes6 2 + elementaryOnes6 3 +
      elementaryOnes6 4 + elementaryOnes6 5 + elementaryOnes6 6 = 2 ^ 6 := by
  native_decide

/-! ## Power sums and Newton identities for small alphabets -/

/-- Elementary symmetric values for the alphabet `(1, 2, 3)`. -/
def elementary123 : Fin 4 → ℕ := ![1, 6, 11, 6]

/-- Power sums `p_k(1, 2, 3)`, for `k = 0, ..., 4`. -/
def power123 : Fin 5 → ℕ := ![3, 6, 14, 36, 98]

/-- Elementary symmetric values for the alphabet `(1, 2, 3, 4)`. -/
def elementary1234 : Fin 5 → ℕ := ![1, 10, 35, 50, 24]

/-- Power sums `p_k(1, 2, 3, 4)`, for `k = 0, ..., 4`. -/
def power1234 : Fin 5 → ℕ := ![4, 10, 30, 100, 354]

theorem power123_second_from_elementary :
    power123 2 = elementary123 1 * power123 1 - 2 * elementary123 2 := by
  native_decide

theorem power123_third_newton :
    (power123 3 : ℤ) =
      (elementary123 1 : ℤ) * (power123 2 : ℤ) -
        (elementary123 2 : ℤ) * (power123 1 : ℤ) +
          3 * (elementary123 3 : ℤ) := by
  native_decide

theorem elementary123_second_from_power :
    ((power123 1) ^ 2 - power123 2) / 2 = elementary123 2 := by
  native_decide

theorem elementary123_third_from_power :
    ((power123 1 : ℤ) ^ 3 - 3 * (power123 1 : ℤ) * (power123 2 : ℤ) +
        2 * (power123 3 : ℤ)) / 6 = elementary123 3 := by
  native_decide

theorem power1234_fourth_newton :
    (power1234 4 : ℤ) =
      (elementary1234 1 : ℤ) * (power1234 3 : ℤ) -
        (elementary1234 2 : ℤ) * (power1234 2 : ℤ) +
          (elementary1234 3 : ℤ) * (power1234 1 : ℤ) -
            4 * (elementary1234 4 : ℤ) := by
  native_decide

/-! ## Monomial symmetric functions at all ones -/

/--
Counts of distinct monomials in four variables for exponent multisets
`(1,0,0,0)`, `(2,2,0,0)`, `(2,1,0,0)`, `(3,1,1,0)`.
-/
def monomialOnes4 : Fin 4 → ℕ := ![4, 6, 12, 12]

theorem monomialOnes4_pair_shape :
    monomialOnes4 1 = Nat.factorial 4 / (Nat.factorial 2 * Nat.factorial 2) := by
  native_decide

theorem monomialOnes4_mixed_shape :
    monomialOnes4 2 = Nat.factorial 4 / Nat.factorial 2 := by
  native_decide

theorem monomialOnes4_shape_table_sum :
    monomialOnes4 0 + monomialOnes4 1 + monomialOnes4 2 + monomialOnes4 3 = 34 := by
  native_decide

/-! ## Schur specializations and hook-length dimensions -/

/-- Hook lengths for the Young shape `(3, 2, 1)`, in row-reading order. -/
def hookLengths321 : Fin 6 → ℕ := ![5, 3, 1, 3, 1, 1]

/-- Hook lengths for the Young shape `(4, 2, 1)`, in row-reading order. -/
def hookLengths421 : Fin 7 → ℕ := ![6, 4, 2, 1, 3, 1, 1]

/-- Hook-content numerator factors for `s_(2,1)(1,1,1)`. -/
def schurContentFactors21In3 : Fin 3 → ℕ := ![3, 4, 2]

/-- Hook lengths for the Young shape `(2, 1)`. -/
def hookLengths21 : Fin 3 → ℕ := ![3, 1, 1]

def hookProduct321 : ℕ :=
  hookLengths321 0 * hookLengths321 1 * hookLengths321 2 *
    hookLengths321 3 * hookLengths321 4 * hookLengths321 5

def hookProduct421 : ℕ :=
  hookLengths421 0 * hookLengths421 1 * hookLengths421 2 * hookLengths421 3 *
    hookLengths421 4 * hookLengths421 5 * hookLengths421 6

def hookProduct21 : ℕ :=
  hookLengths21 0 * hookLengths21 1 * hookLengths21 2

def schurContentProduct21In3 : ℕ :=
  schurContentFactors21In3 0 * schurContentFactors21In3 1 *
    schurContentFactors21In3 2

theorem hookProduct321_value :
    hookProduct321 = 45 := by
  native_decide

theorem standardTableaux321_hook_formula :
    Nat.factorial 6 / hookProduct321 = 16 := by
  native_decide

theorem standardTableaux421_hook_formula :
    Nat.factorial 7 / hookProduct421 = 35 := by
  native_decide

theorem schur21_at_three_ones_hook_content :
    schurContentProduct21In3 / hookProduct21 = 8 := by
  native_decide

/-! ## RSK and Newton cross-check tables -/

/-- The values `f^λ` for partitions of `5`, ordered lexicographically by shape. -/
def standardTableauxOfFive : Fin 7 → ℕ := ![1, 4, 5, 6, 5, 4, 1]

/-- First six involution numbers, used as `Σ f^λ` checks under RSK. -/
def involutionNumbers : Fin 6 → ℕ := ![1, 1, 2, 4, 10, 26]

theorem rsk_square_sum_five :
    (standardTableauxOfFive 0) ^ 2 + (standardTableauxOfFive 1) ^ 2 +
      (standardTableauxOfFive 2) ^ 2 + (standardTableauxOfFive 3) ^ 2 +
        (standardTableauxOfFive 4) ^ 2 + (standardTableauxOfFive 5) ^ 2 +
          (standardTableauxOfFive 6) ^ 2 = Nat.factorial 5 := by
  native_decide

theorem rsk_involution_sum_five :
    standardTableauxOfFive 0 + standardTableauxOfFive 1 + standardTableauxOfFive 2 +
      standardTableauxOfFive 3 + standardTableauxOfFive 4 + standardTableauxOfFive 5 +
        standardTableauxOfFive 6 = involutionNumbers 5 := by
  native_decide

theorem newton_table_consistency :
    (elementary1234 1 : ℤ) ^ 4 - 4 * (elementary1234 1 : ℤ) ^ 2 *
        (elementary1234 2 : ℤ) + 2 * (elementary1234 2 : ℤ) ^ 2 +
      4 * (elementary1234 1 : ℤ) * (elementary1234 3 : ℤ) -
        4 * (elementary1234 4 : ℤ) = power1234 4 := by
  native_decide

end SymmetricFunctions
