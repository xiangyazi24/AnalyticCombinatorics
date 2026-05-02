/-
  Analytic Combinatorics — Part B: Complex Asymptotics
  Chapter VI — Mellin Transform & Harmonic Sums

  Harmonic numbers and related discrete sums arise naturally in the
  analysis of algorithms (Quicksort, digital trees, etc.) and connect
  to the Mellin transform framework of Chapter VI.

  This file formalizes:
  1. Harmonic numbers H_n = Σ_{k=1}^n 1/k
  2. Generalized harmonic numbers H_n^{(r)} = Σ_{k=1}^n 1/k^r
  3. Alternating harmonic partial sums
  4. Digital sum (popcount / number of 1-bits)
  5. Number of binary digits

  Reference: F&S § VI.7–VI.8, Knuth TAOCP Vol. 1 § 1.2.7.
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace MellinHarmonicSums

/-! ## 1. Harmonic numbers H_n -/

/-- The n-th harmonic number H_n = Σ_{k=1}^n 1/k, computed as a rational. -/
def harmonicRat (n : ℕ) : ℚ := ∑ k ∈ Finset.range n, 1 / ((k + 1) : ℚ)

theorem harmonicRat_one : harmonicRat 1 = 1 := by native_decide

theorem harmonicRat_two : harmonicRat 2 = 3 / 2 := by native_decide

theorem harmonicRat_three : harmonicRat 3 = 11 / 6 := by native_decide

theorem harmonicRat_four : harmonicRat 4 = 25 / 12 := by native_decide

theorem harmonicRat_five : harmonicRat 5 = 137 / 60 := by native_decide

theorem harmonicRat_six : harmonicRat 6 = 49 / 20 := by native_decide

/-! ## 2. Generalized harmonic numbers H_n^{(r)} -/

/-- The generalized harmonic number H_n^{(r)} = Σ_{k=1}^n 1/k^r. -/
def generalizedHarmonic (r n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range n, 1 / ((k + 1) : ℚ) ^ r

theorem generalizedHarmonic_two_four :
    generalizedHarmonic 2 4 = 205 / 144 := by native_decide

/-- H_n^{(1)} = H_n (spot checks). -/
theorem generalizedHarmonic_one_eq_harmonicRat_1 :
    generalizedHarmonic 1 1 = harmonicRat 1 := by native_decide

theorem generalizedHarmonic_one_eq_harmonicRat_2 :
    generalizedHarmonic 1 2 = harmonicRat 2 := by native_decide

theorem generalizedHarmonic_one_eq_harmonicRat_3 :
    generalizedHarmonic 1 3 = harmonicRat 3 := by native_decide

theorem generalizedHarmonic_one_eq_harmonicRat_4 :
    generalizedHarmonic 1 4 = harmonicRat 4 := by native_decide

/-! ## 3. Alternating harmonic partial sums -/

/-- Alternating harmonic partial sum: Σ_{k=0}^{n-1} (-1)^k / (k+1). -/
def alternatingHarmonic (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range n, (-1 : ℚ) ^ k / ((k + 1) : ℚ)

theorem alternatingHarmonic_one : alternatingHarmonic 1 = 1 := by native_decide

theorem alternatingHarmonic_two : alternatingHarmonic 2 = 1 / 2 := by native_decide

theorem alternatingHarmonic_three : alternatingHarmonic 3 = 5 / 6 := by native_decide

theorem alternatingHarmonic_four : alternatingHarmonic 4 = 7 / 12 := by native_decide

/-! ## 4. Digital sum (popcount) -/

/-- Digital sum: the number of 1-bits in the binary representation of n. -/
def digitSum : ℕ → ℕ
  | 0 => 0
  | n + 1 => ((n + 1) % 2) + digitSum ((n + 1) / 2)
termination_by n => n
decreasing_by omega

/-- Total digit sum property: Σ_{i=0}^{2^k - 1} digitSum(i) = k * 2^{k-1}.
    Verified for small k using native_decide. -/
theorem digitSum_total_k1 :
    ∑ i ∈ Finset.range (2 ^ 1), digitSum i = 1 * 2 ^ 0 := by native_decide

theorem digitSum_total_k2 :
    ∑ i ∈ Finset.range (2 ^ 2), digitSum i = 2 * 2 ^ 1 := by native_decide

theorem digitSum_total_k3 :
    ∑ i ∈ Finset.range (2 ^ 3), digitSum i = 3 * 2 ^ 2 := by native_decide

theorem digitSum_total_k4 :
    ∑ i ∈ Finset.range (2 ^ 4), digitSum i = 4 * 2 ^ 3 := by native_decide

theorem digitSum_total_k5 :
    ∑ i ∈ Finset.range (2 ^ 5), digitSum i = 5 * 2 ^ 4 := by native_decide

/-! ## 5. Number of binary digits -/

/-- The number of binary digits of n (with convention binaryDigits 0 = 1). -/
def binaryDigits (n : ℕ) : ℕ := if n = 0 then 1 else Nat.log 2 n + 1

theorem binaryDigits_seven : binaryDigits 7 = 3 := by native_decide

theorem binaryDigits_eight : binaryDigits 8 = 4 := by native_decide

theorem binaryDigits_fifteen : binaryDigits 15 = 4 := by native_decide

theorem binaryDigits_sixteen : binaryDigits 16 = 5 := by native_decide

end MellinHarmonicSums
