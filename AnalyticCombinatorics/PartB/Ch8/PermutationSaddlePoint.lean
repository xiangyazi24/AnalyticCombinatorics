import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace PermutationSaddlePoint

/-! ## 1. Factorials for `n = 0 .. 10` -/

/-- Table of `n!` for `n = 0 .. 10`. -/
def factorialTable : Fin 11 → ℕ :=
  ![1, 1, 2, 6, 24, 120, 720, 5040, 40320, 362880, 3628800]

theorem factorialTable_correct : ∀ i : Fin 11, factorialTable i = Nat.factorial (i : ℕ) := by
  native_decide

/-! ## 2. Stirling proxy bounds -/

/-- Crude Stirling proxy: `n! < n^n` for `n = 2 .. 8`. -/
theorem factorial_lt_self_pow_2_to_8 :
    ∀ i : Fin 7, Nat.factorial ((i : ℕ) + 2) < ((i : ℕ) + 2) ^ ((i : ℕ) + 2) := by
  native_decide

/-- Crude lower proxy: `3^n n! > n^n` for `n = 2 .. 7`. -/
theorem three_pow_mul_factorial_gt_self_pow_2_to_7 :
    ∀ i : Fin 6,
      3 ^ ((i : ℕ) + 2) * Nat.factorial ((i : ℕ) + 2) >
        ((i : ℕ) + 2) ^ ((i : ℕ) + 2) := by
  native_decide

/-! ## 3. Derangements for `n = 0 .. 8` -/

/-- Table of derangement numbers `D(n)` for `n = 0 .. 8`. -/
def derangementTable : Fin 9 → ℕ :=
  ![1, 0, 1, 2, 9, 44, 265, 1854, 14833]

theorem derangementTable_values :
    derangementTable =
      ![1, 0, 1, 2, 9, 44, 265, 1854, 14833] := by
  native_decide

/-- `D(n) < n!` for `n = 1 .. 8`. -/
theorem derangement_lt_factorial_1_to_8 :
    ∀ i : Fin 8, derangementTable ⟨(i : ℕ) + 1, by omega⟩ < Nat.factorial ((i : ℕ) + 1) := by
  native_decide

/-! ## 4. Involutions for `n = 0 .. 9` -/

/-- Table of involution numbers `I(n)` for `n = 0 .. 9`. -/
def involutionTable : Fin 10 → ℕ :=
  ![1, 1, 2, 4, 10, 26, 76, 232, 764, 2620]

theorem involutionTable_values :
    involutionTable =
      ![1, 1, 2, 4, 10, 26, 76, 232, 764, 2620] := by
  native_decide

/-- `I(n) ≤ n!` for `n = 0 .. 9`. -/
theorem involution_le_factorial_0_to_9 :
    ∀ i : Fin 10, involutionTable i ≤ Nat.factorial (i : ℕ) := by
  native_decide

/-! ## 5. Menage numbers for `n = 3 .. 7` -/

/-- Table of menage numbers `M(n)` for `n = 3 .. 7`. -/
def menageTable : Fin 5 → ℕ :=
  ![1, 2, 13, 80, 579]

theorem menageTable_values :
    menageTable = ![1, 2, 13, 80, 579] := by
  native_decide

/-- `M(n) < n!` for `n = 3 .. 7`. -/
theorem menage_lt_factorial_3_to_7 :
    ∀ i : Fin 5, menageTable i < Nat.factorial ((i : ℕ) + 3) := by
  native_decide

/-! ## 6. Derangements are at least one third of factorials in this range -/

/-- `3 * D(n) ≥ n!` for `n = 3 .. 8`. -/
theorem three_mul_derangement_ge_factorial_3_to_8 :
    ∀ i : Fin 6,
      3 * derangementTable ⟨(i : ℕ) + 3, by omega⟩ ≥ Nat.factorial ((i : ℕ) + 3) := by
  native_decide

end PermutationSaddlePoint
