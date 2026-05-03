/-
  Analytic Combinatorics — Part B: Complex Asymptotics
  Chapter VI/VIII — Euler-Maclaurin summation, Bernoulli numbers, zeta partial sums.
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace EulerMaclaurin

/-! ## Bernoulli numbers B_0 through B_10 (as rationals) -/

/-- The first 11 Bernoulli numbers: B_0, B_1, ..., B_10. -/
def bernoulliTable : Fin 11 → ℚ :=
  ![(1 : ℚ), -1/2, 1/6, 0, -1/30, 0, 1/42, 0, -1/30, 0, 5/66]

-- Spot-checks on individual values
theorem bernoulliTable_zero : bernoulliTable 0 = 1 := by native_decide
theorem bernoulliTable_one : bernoulliTable 1 = -1/2 := by native_decide
theorem bernoulliTable_two : bernoulliTable 2 = 1/6 := by native_decide
theorem bernoulliTable_three : bernoulliTable 3 = 0 := by native_decide
theorem bernoulliTable_four : bernoulliTable 4 = -1/30 := by native_decide
theorem bernoulliTable_five : bernoulliTable 5 = 0 := by native_decide
theorem bernoulliTable_six : bernoulliTable 6 = 1/42 := by native_decide
theorem bernoulliTable_ten : bernoulliTable 10 = 5/66 := by native_decide

/-! ## Partial sums of Bernoulli numbers -/

/-- B_0 + B_1 + B_2 = 1 - 1/2 + 1/6 = 2/3 -/
theorem bernoulli_sum_012 :
    bernoulliTable 0 + bernoulliTable 1 + bernoulliTable 2 = 2/3 := by native_decide

/-! ## Bernoulli recurrence identity: Σ_{k=0}^{n} C(n+1,k) * B_k = 0 for n ≥ 1 -/

/-- For n=1: C(2,0)*B_0 + C(2,1)*B_1 = 1 + 2*(-1/2) = 0 -/
theorem bernoulli_recurrence_n1 :
    (Nat.choose 2 0 : ℚ) * bernoulliTable 0 +
    (Nat.choose 2 1 : ℚ) * bernoulliTable 1 = 0 := by native_decide

/-- For n=2: C(3,0)*B_0 + C(3,1)*B_1 + C(3,2)*B_2 = 1 - 3/2 + 3/6 = 0 -/
theorem bernoulli_recurrence_n2 :
    (Nat.choose 3 0 : ℚ) * bernoulliTable 0 +
    (Nat.choose 3 1 : ℚ) * bernoulliTable 1 +
    (Nat.choose 3 2 : ℚ) * bernoulliTable 2 = 0 := by native_decide

/-- For n=3: C(4,0)*B_0 + C(4,1)*B_1 + C(4,2)*B_2 + C(4,3)*B_3 = 1 - 2 + 1 + 0 = 0 -/
theorem bernoulli_recurrence_n3 :
    (Nat.choose 4 0 : ℚ) * bernoulliTable 0 +
    (Nat.choose 4 1 : ℚ) * bernoulliTable 1 +
    (Nat.choose 4 2 : ℚ) * bernoulliTable 2 +
    (Nat.choose 4 3 : ℚ) * bernoulliTable 3 = 0 := by native_decide

/-! ## Power sums S_k(n) = Σ_{i=1}^{n} i^k -/

/-- S_k(n) = Σ_{i=1}^{n} i^k, computed as Σ_{i ∈ range n} (i+1)^k. -/
def powerSum (k n : ℕ) : ℕ := ∑ i ∈ Finset.range n, (i + 1) ^ k

-- S_1(10) = 1+2+...+10 = 55
theorem powerSum_1_10 : powerSum 1 10 = 55 := by native_decide

-- S_2(10) = 1^2+2^2+...+10^2 = 385
theorem powerSum_2_10 : powerSum 2 10 = 385 := by native_decide

-- S_3(10) = 1^3+2^3+...+10^3 = 3025 = 55^2
theorem powerSum_3_10 : powerSum 3 10 = 3025 := by native_decide

theorem powerSum_3_10_eq_sq : powerSum 3 10 = (powerSum 1 10) ^ 2 := by native_decide

/-! ## Nicomachus theorem: S_3(n) = (S_1(n))^2 for small n -/

theorem nicomachus_1 : powerSum 3 1 = (powerSum 1 1) ^ 2 := by native_decide
theorem nicomachus_2 : powerSum 3 2 = (powerSum 1 2) ^ 2 := by native_decide
theorem nicomachus_3 : powerSum 3 3 = (powerSum 1 3) ^ 2 := by native_decide
theorem nicomachus_4 : powerSum 3 4 = (powerSum 1 4) ^ 2 := by native_decide
theorem nicomachus_5 : powerSum 3 5 = (powerSum 1 5) ^ 2 := by native_decide
theorem nicomachus_6 : powerSum 3 6 = (powerSum 1 6) ^ 2 := by native_decide
theorem nicomachus_7 : powerSum 3 7 = (powerSum 1 7) ^ 2 := by native_decide
theorem nicomachus_8 : powerSum 3 8 = (powerSum 1 8) ^ 2 := by native_decide

/-! ## Partial sums of ζ(2) = Σ_{k=1}^∞ 1/k² -/

/-- Rational partial sums of ζ(2): Σ_{k=1}^{n} 1/k². -/
def zetaPartial2 (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range n, 1 / ((k + 1 : ℚ)) ^ 2

-- zetaPartial2 1 = 1
theorem zetaPartial2_1 : zetaPartial2 1 = 1 := by native_decide

-- zetaPartial2 2 = 1 + 1/4 = 5/4
theorem zetaPartial2_2 : zetaPartial2 2 = 5/4 := by native_decide

-- zetaPartial2 3 = 1 + 1/4 + 1/9 = 49/36
theorem zetaPartial2_3 : zetaPartial2 3 = 49/36 := by native_decide

-- zetaPartial2 4 = 1 + 1/4 + 1/9 + 1/16 = 205/144
theorem zetaPartial2_4 : zetaPartial2 4 = 205/144 := by native_decide

-- zetaPartial2 5 = 1 + 1/4 + 1/9 + 1/16 + 1/25 = 5269/3600
theorem zetaPartial2_5 : zetaPartial2 5 = 5269/3600 := by native_decide

/-! ## Euler-Maclaurin: bounding the partial sums (ζ(2) = π²/6 < 2) -/

-- zetaPartial2 5 ≈ 1.4636, which is already > 1 and < 2
example : zetaPartial2 5 > 1 := by native_decide

example : zetaPartial2 5 < 2 := by native_decide

-- At n=10, ζ₁₀ ≈ 1.5498, which exceeds 3/2 and is still below 2
example : zetaPartial2 10 > 3/2 := by native_decide

example : zetaPartial2 10 < 2 := by native_decide

/-! ## Faulhaber's formula: sum of fourth powers -/

/-- Sum of fourth powers: Σ_{i=1}^{n} i^4. -/
def sumFourthPow (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, (i + 1) ^ 4

-- sumFourthPow 1 = 1
theorem sumFourthPow_1 : sumFourthPow 1 = 1 := by native_decide

-- sumFourthPow 2 = 1 + 16 = 17
theorem sumFourthPow_2 : sumFourthPow 2 = 17 := by native_decide

-- sumFourthPow 3 = 1 + 16 + 81 = 98
theorem sumFourthPow_3 : sumFourthPow 3 = 98 := by native_decide

-- sumFourthPow 4 = 1 + 16 + 81 + 256 = 354
theorem sumFourthPow_4 : sumFourthPow 4 = 354 := by native_decide

-- sumFourthPow 5 = 1 + 16 + 81 + 256 + 625 = 979
theorem sumFourthPow_5 : sumFourthPow 5 = 979 := by native_decide

/-! ## Connection: powerSum via Finset.range agrees with direct sum -/

-- Cross-check: powerSum 4 5 = sumFourthPow 5
theorem powerSum_4_5_eq_sumFourthPow_5 : powerSum 4 5 = sumFourthPow 5 := by native_decide

-- Gauss formula: S_1(n) = n*(n+1)/2. Check n=1..10 inline.
theorem gauss_formula_10 : powerSum 1 10 * 2 = 10 * 11 := by native_decide

-- S_2(n) = n*(n+1)*(2n+1)/6. Check n=10.
theorem square_sum_formula_10 : powerSum 2 10 * 6 = 10 * 11 * 21 := by native_decide

end EulerMaclaurin
