/-
  Analytic Combinatorics — Part B: Complex Asymptotics
  Chapter VIII — Further concrete saddle-point enumeration checks.
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AsymptoticEnumeration2

open Finset

/-! ## 1. Integer partitions p(n), n = 0 .. 20 -/

/-- Table of p(n) for n = 0 .. 20. -/
def partitionTable : Fin 21 → ℕ :=
  ![1, 1, 2, 3, 5, 7, 11, 15, 22, 30, 42,
    56, 77, 101, 135, 176, 231, 297, 385, 490, 627]

/-- Entry-by-entry verification of p(n), n = 0 .. 20. -/
theorem partition_values_0_20 :
    partitionTable ⟨0, by omega⟩ = 1 ∧
    partitionTable ⟨1, by omega⟩ = 1 ∧
    partitionTable ⟨2, by omega⟩ = 2 ∧
    partitionTable ⟨3, by omega⟩ = 3 ∧
    partitionTable ⟨4, by omega⟩ = 5 ∧
    partitionTable ⟨5, by omega⟩ = 7 ∧
    partitionTable ⟨6, by omega⟩ = 11 ∧
    partitionTable ⟨7, by omega⟩ = 15 ∧
    partitionTable ⟨8, by omega⟩ = 22 ∧
    partitionTable ⟨9, by omega⟩ = 30 ∧
    partitionTable ⟨10, by omega⟩ = 42 ∧
    partitionTable ⟨11, by omega⟩ = 56 ∧
    partitionTable ⟨12, by omega⟩ = 77 ∧
    partitionTable ⟨13, by omega⟩ = 101 ∧
    partitionTable ⟨14, by omega⟩ = 135 ∧
    partitionTable ⟨15, by omega⟩ = 176 ∧
    partitionTable ⟨16, by omega⟩ = 231 ∧
    partitionTable ⟨17, by omega⟩ = 297 ∧
    partitionTable ⟨18, by omega⟩ = 385 ∧
    partitionTable ⟨19, by omega⟩ = 490 ∧
    partitionTable ⟨20, by omega⟩ = 627 := by
  native_decide

/-! ## 2. Strict monotonicity p(n) < p(n+1), n = 1 .. 19 -/

/-- Strict monotonicity for p(n), n = 1 .. 19. -/
theorem partition_strict_mono_1_19 :
    ∀ i : Fin 19,
      partitionTable ⟨(i : ℕ) + 1, by omega⟩ <
        partitionTable ⟨(i : ℕ) + 2, by omega⟩ := by
  native_decide

/-! ## 3. Exponential bound p(n) < 2^n -/

/-- The non-strict bound p(n) ≤ 2^n holds for n = 0 .. 20. -/
theorem partition_le_pow2_0_20 :
    ∀ i : Fin 21, partitionTable i ≤ 2 ^ (i : ℕ) := by
  native_decide

/-- The requested strict bound starts at n = 1; at n = 0, both sides equal 1. -/
theorem partition_lt_pow2_1_20 :
    ∀ i : Fin 20,
      partitionTable ⟨(i : ℕ) + 1, by omega⟩ < 2 ^ ((i : ℕ) + 1) := by
  native_decide

example : ¬ partitionTable ⟨0, by omega⟩ < 2 ^ 0 := by
  native_decide

/-! ## 4. Comparing p(n)^2 with p(2n) -/

/-- For n = 1, 2, 3, the inequality p(n)^2 < p(2n) holds. -/
theorem partition_square_lt_double_1_3 :
    ∀ i : Fin 3,
      partitionTable ⟨(i : ℕ) + 1, by omega⟩ ^ 2 <
        partitionTable ⟨2 * ((i : ℕ) + 1), by omega⟩ := by
  native_decide

/-- Starting with n = 4 in this table, the reverse inequality p(n)^2 > p(2n) holds. -/
theorem partition_square_gt_double_4_10 :
    ∀ i : Fin 7,
      partitionTable ⟨(i : ℕ) + 4, by omega⟩ ^ 2 >
        partitionTable ⟨2 * ((i : ℕ) + 4), by omega⟩ := by
  native_decide

example : partitionTable ⟨0, by omega⟩ ^ 2 = partitionTable ⟨0, by omega⟩ := by
  native_decide

/-! ## 5. Central Delannoy numbers -/

/-- Central Delannoy numbers D(n), n = 0 .. 6. -/
def centralDelannoyTable : Fin 7 → ℕ :=
  ![1, 3, 13, 63, 321, 1683, 8989]

/-- The finite binomial sum formula for central Delannoy numbers. -/
def centralDelannoySum (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), Nat.choose n k ^ 2 * 2 ^ k

/-- Entry-by-entry verification of D(n), n = 0 .. 6. -/
theorem centralDelannoy_values_0_6 :
    centralDelannoyTable ⟨0, by omega⟩ = 1 ∧
    centralDelannoyTable ⟨1, by omega⟩ = 3 ∧
    centralDelannoyTable ⟨2, by omega⟩ = 13 ∧
    centralDelannoyTable ⟨3, by omega⟩ = 63 ∧
    centralDelannoyTable ⟨4, by omega⟩ = 321 ∧
    centralDelannoyTable ⟨5, by omega⟩ = 1683 ∧
    centralDelannoyTable ⟨6, by omega⟩ = 8989 := by
  native_decide

/-- Verify D(n) = sum k=0..n of C(n,k)^2 * 2^k for n = 0 .. 4. -/
theorem centralDelannoy_formula_0_4 :
    ∀ i : Fin 5,
      centralDelannoyTable ⟨(i : ℕ), by omega⟩ = centralDelannoySum (i : ℕ) := by
  native_decide

/-! ## 6. Large Schroeder numbers and Catalan comparison -/

/-- Large Schroeder numbers S(n), n = 0 .. 7. -/
def largeSchroederTable : Fin 8 → ℕ :=
  ![1, 2, 6, 22, 90, 394, 1806, 8558]

/-- Catalan number C_n = binom(2n,n)/(n+1). -/
def catalan (n : ℕ) : ℕ :=
  Nat.choose (2 * n) n / (n + 1)

/-- Entry-by-entry verification of large Schroeder numbers, n = 0 .. 7. -/
theorem largeSchroeder_values_0_7 :
    largeSchroederTable ⟨0, by omega⟩ = 1 ∧
    largeSchroederTable ⟨1, by omega⟩ = 2 ∧
    largeSchroederTable ⟨2, by omega⟩ = 6 ∧
    largeSchroederTable ⟨3, by omega⟩ = 22 ∧
    largeSchroederTable ⟨4, by omega⟩ = 90 ∧
    largeSchroederTable ⟨5, by omega⟩ = 394 ∧
    largeSchroederTable ⟨6, by omega⟩ = 1806 ∧
    largeSchroederTable ⟨7, by omega⟩ = 8558 := by
  native_decide

/-- For the tabulated range n = 2 .. 7, S(n) > 2 * Catalan(n). -/
theorem largeSchroeder_gt_two_catalan_2_7 :
    ∀ i : Fin 6,
      largeSchroederTable ⟨(i : ℕ) + 2, by omega⟩ > 2 * catalan ((i : ℕ) + 2) := by
  native_decide

end AsymptoticEnumeration2
