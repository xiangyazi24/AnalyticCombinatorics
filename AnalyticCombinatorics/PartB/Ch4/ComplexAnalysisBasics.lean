/-
  Analytic Combinatorics — Part B: Complex Asymptotics
  Chapter IV — Complex Analysis Basics

  Coefficient extraction, geometric sums, Newton's identities,
  partial fractions, and exponential partial sum bounds.
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace ComplexAnalysisBasics

/-! ## 1. Polynomial coefficient extraction -/

/-- Extract the n-th coefficient from a polynomial given as a list. -/
def polyCoeff (coeffs : List ℚ) (n : ℕ) : ℚ := coeffs.getD n 0

theorem polyCoeff_0 : polyCoeff [1, 2, 3] 0 = 1 := by native_decide
theorem polyCoeff_1 : polyCoeff [1, 2, 3] 1 = 2 := by native_decide
theorem polyCoeff_2 : polyCoeff [1, 2, 3] 2 = 3 := by native_decide
theorem polyCoeff_3 : polyCoeff [1, 2, 3] 3 = 0 := by native_decide

/-! ## 2. Geometric sum formula -/

/-- Check that (r-1) * Σ_{k=0}^n r^k + 1 = r^{n+1} for natural numbers. -/
def geomSumCheck (r n : ℕ) : Bool :=
  (r - 1) * (∑ k ∈ Finset.range (n + 1), r ^ k) + 1 == r ^ (n + 1)

theorem geomSum_r2_n1 : geomSumCheck 2 1 = true := by native_decide
theorem geomSum_r2_n4 : geomSumCheck 2 4 = true := by native_decide
theorem geomSum_r2_n8 : geomSumCheck 2 8 = true := by native_decide
theorem geomSum_r3_n1 : geomSumCheck 3 1 = true := by native_decide
theorem geomSum_r3_n5 : geomSumCheck 3 5 = true := by native_decide
theorem geomSum_r3_n8 : geomSumCheck 3 8 = true := by native_decide
theorem geomSum_r4_n3 : geomSumCheck 4 3 = true := by native_decide
theorem geomSum_r4_n8 : geomSumCheck 4 8 = true := by native_decide
theorem geomSum_r5_n2 : geomSumCheck 5 2 = true := by native_decide
theorem geomSum_r5_n8 : geomSumCheck 5 8 = true := by native_decide

/-! ## 3. Newton's identities (power sums ↔ elementary symmetric) -/

/-- For two integers x₁, x₂: p₂ = e₁² - 2e₂ where e₁ = x₁+x₂, e₂ = x₁*x₂. -/
def newtonIdentityCheck (x1 x2 : ℤ) : Bool :=
  let e1 := x1 + x2
  let e2 := x1 * x2
  let p2 := x1 ^ 2 + x2 ^ 2
  p2 == e1 ^ 2 - 2 * e2

theorem newton_1_2 : newtonIdentityCheck 1 2 = true := by native_decide
theorem newton_2_3 : newtonIdentityCheck 2 3 = true := by native_decide
theorem newton_3_5 : newtonIdentityCheck 3 5 = true := by native_decide
theorem newton_neg1_4 : newtonIdentityCheck (-1) 4 = true := by native_decide

/-! ## 4. Partial fractions / rational GF coefficient extraction -/

/-- [z^n] 1/((1-z)(1-2z)) = 2^{n+1} - 1. -/
def rationalGFCoeff (n : ℕ) : ℤ := 2 ^ (n + 1) - 1

theorem rationalGF_0 : rationalGFCoeff 0 = 1 := by native_decide
theorem rationalGF_1 : rationalGFCoeff 1 = 3 := by native_decide
theorem rationalGF_2 : rationalGFCoeff 2 = 7 := by native_decide
theorem rationalGF_3 : rationalGFCoeff 3 = 15 := by native_decide
theorem rationalGF_4 : rationalGFCoeff 4 = 31 := by native_decide

/-- Cross-check via convolution: Σ_{k=0}^n 2^k = 2^{n+1} - 1. -/
def convCheck (n : ℕ) : Bool :=
  (∑ k ∈ Finset.range (n + 1), (2 : ℤ) ^ k) == 2 ^ (n + 1) - 1

theorem conv_0 : convCheck 0 = true := by native_decide
theorem conv_1 : convCheck 1 = true := by native_decide
theorem conv_2 : convCheck 2 = true := by native_decide
theorem conv_3 : convCheck 3 = true := by native_decide
theorem conv_4 : convCheck 4 = true := by native_decide
theorem conv_8 : convCheck 8 = true := by native_decide

/-! ## 5. Exponential partial sums bound -/

/-- Partial sum of the exponential series: Σ_{k=0}^n 1/k! as a rational number. -/
def expPartialSumQ (n : ℕ) : ℚ := ∑ k ∈ Finset.range (n + 1), 1 / (Nat.factorial k : ℚ)

theorem expPartialSum_1 : expPartialSumQ 1 = 2 := by native_decide
theorem expPartialSum_5 : expPartialSumQ 5 = 163 / 60 := by native_decide
theorem expPartialSum_10_lt_3 : expPartialSumQ 10 < 3 := by native_decide

end ComplexAnalysisBasics
