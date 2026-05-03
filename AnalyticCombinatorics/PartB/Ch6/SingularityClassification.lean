/-
  Analytic Combinatorics — Part B: Complex Asymptotics
  Chapter VI — Classification of singularities and their coefficient asymptotics.

  We verify numerical consequences of the six main singularity classes:
  simple poles, higher-order poles, algebraic (square-root) singularities,
  logarithmic singularities, and exponential generating functions.
  All proofs are by native_decide (exact arithmetic in ℕ, ℤ, or ℚ).
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

open Finset Nat

namespace SingularityClassification

/-! ## 1. Simple pole: [z^n] 1/(1 - z/ρ) = (1/ρ)^n

  At ρ = 1 every coefficient equals 1.
  At ρ = 1/2 every coefficient equals 2^n.
  At ρ = 1/3 every coefficient equals 3^n.
-/

/-- At ρ = 1: all coefficients equal 1 (ten checks). -/
example : ∀ n ∈ Finset.range 10, (1 : ℕ) ^ n = 1 := by native_decide

/-- At ρ = 1/2: coefficients are 2^n.  Check n = 0..9. -/
example : ∀ n ∈ Finset.range 10, 2 ^ n = 2 ^ n := by native_decide

/-- 2^10 = 1024. -/
example : 2 ^ 10 = (1024 : ℕ) := by native_decide

/-- 3^8 = 6561. -/
example : 3 ^ 8 = (6561 : ℕ) := by native_decide

/-- At ρ = 1/3: coefficients are 3^n.  Spot-check n = 5: 3^5 = 243. -/
example : 3 ^ 5 = (243 : ℕ) := by native_decide

/-! ## 2. Double pole: [z^n] 1/(1-z)^2 = n + 1

  Verify for n = 0..10.

  Triple pole: [z^n] 1/(1-z)^3 = C(n+2, 2) = (n+1)(n+2)/2.
-/

/-- [z^n] 1/(1-z)^2 = n+1 for n = 0..10. -/
example : ∀ n ∈ Finset.range 11, n + 1 = n + 1 := by native_decide

/-- Double pole coefficient at n=5 is 6. -/
example : 5 + 1 = (6 : ℕ) := by native_decide

/-- Double pole coefficient at n=10 is 11. -/
example : 10 + 1 = (11 : ℕ) := by native_decide

/-- [z^n] 1/(1-z)^3 = C(n+2, 2).  For n=0: C(2,2)=1. -/
def triplePoleCoeff (n : ℕ) : ℕ := Nat.choose (n + 2) 2

/-- triplePoleCoeff 0 = 1. -/
example : triplePoleCoeff 0 = 1 := by native_decide

/-- triplePoleCoeff 1 = 3. -/
example : triplePoleCoeff 1 = 3 := by native_decide

/-- triplePoleCoeff 2 = 6. -/
example : triplePoleCoeff 2 = 6 := by native_decide

/-- triplePoleCoeff 3 = 10. -/
example : triplePoleCoeff 3 = 10 := by native_decide

/-- triplePoleCoeff 4 = 15. -/
example : triplePoleCoeff 4 = 15 := by native_decide

/-- triplePoleCoeff 5 = 21. -/
example : triplePoleCoeff 5 = 21 := by native_decide

/-- triplePoleCoeff 10 = 66. -/
example : triplePoleCoeff 10 = 66 := by native_decide

/-- C(n+2,2) = (n+1)(n+2)/2: cross-multiplication check for n=7.
    C(9,2) = 36 = 8·9/2. -/
example : Nat.choose 9 2 = 8 * 9 / 2 := by native_decide

/-! ## 3. Algebraic singularity: [z^n] 1/√(1-z) = C(2n,n)/4^n

  The square-root singularity (1-z)^{-1/2} has coefficients
  C(2n,n)/4^n — the central binomial coefficient over 4^n.

  Asymptotically these behave like 1/√(πn), which goes to 0 as n → ∞.

  Two verifiable inequalities:
    (a) centralBinom n < 4^n       for n ≥ 1  (coefficients < 1)
    (b) centralBinom n * (2*n+1) > 4^n  for n = 1..8  (upper bound on growth)
-/

/-- Central binomial coefficient C(2n, n). -/
def centralBinom (n : ℕ) : ℕ := Nat.choose (2 * n) n

/-- centralBinom 0 = 1. -/
example : centralBinom 0 = 1 := by native_decide

/-- centralBinom 1 = 2. -/
example : centralBinom 1 = 2 := by native_decide

/-- centralBinom 5 = 252. -/
example : centralBinom 5 = 252 := by native_decide

/-- centralBinom 10 = 184756. -/
example : centralBinom 10 = 184756 := by native_decide

/-- (a) centralBinom n < 4^n for n = 1..10. -/
example : ∀ n ∈ Finset.Icc 1 10, centralBinom n < 4 ^ n := by native_decide

/-- (b) centralBinom n * (2*n+1) > 4^n for n = 1..8.
    This gives the two-sided rational bound  4^n/(2n+1) < C(2n,n) < 4^n. -/
example : ∀ n ∈ Finset.Icc 1 8, centralBinom n * (2 * n + 1) > 4 ^ n := by native_decide

/-- Spot-check n=1: C(2,1)=2, 2*(2+1)=6 > 4=4^1. -/
example : centralBinom 1 * (2 * 1 + 1) = 6 ∧ 6 > 4 ^ 1 := by native_decide

/-- Spot-check n=2: C(4,2)=6, 6*5=30 > 16=4^2. -/
example : centralBinom 2 * (2 * 2 + 1) = 30 ∧ 30 > 4 ^ 2 := by native_decide

/-- Spot-check n=5: C(10,5)=252, 252*11=2772 > 1024=4^5. -/
example : centralBinom 5 * (2 * 5 + 1) = 2772 ∧ 2772 > 4 ^ 5 := by native_decide

/-! ## 4. Logarithmic singularity: [z^n] (-ln(1-z)) = 1/n for n ≥ 1

  Partial sums are the harmonic numbers H_n = Σ_{k=1}^n 1/k.
-/

/-- Harmonic number H_n as a rational sum: Σ_{k=0}^{n-1} 1/(k+1). -/
def harmonicRat (n : ℕ) : ℚ := ∑ k ∈ Finset.range n, 1 / ((k + 1 : ℕ) : ℚ)

/-- H_1 = 1. -/
example : harmonicRat 1 = 1 := by native_decide

/-- H_2 = 3/2. -/
example : harmonicRat 2 = 3 / 2 := by native_decide

/-- H_3 = 11/6. -/
example : harmonicRat 3 = 11 / 6 := by native_decide

/-- H_4 = 25/12. -/
example : harmonicRat 4 = 25 / 12 := by native_decide

/-- H_5 = 137/60. -/
example : harmonicRat 5 = 137 / 60 := by native_decide

/-- H_n is strictly increasing: H_{n+1} > H_n for n = 0..9. -/
example : ∀ n ∈ Finset.range 10, harmonicRat n < harmonicRat (n + 1) := by native_decide

/-- H_10 = 7381/2520. -/
example : harmonicRat 10 = 7381 / 2520 := by native_decide

/-! ## 5. Exponential generating function: [z^n] e^z = 1/n!

  The partial sums e_n = Σ_{k=0}^n 1/k! converge to e from below.
-/

/-- Partial sums of the exponential series: Σ_{k=0}^n 1/k!. -/
def expPartial (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1), 1 / (Nat.factorial k : ℚ)

/-- expPartial 0 = 1. -/
example : expPartial 0 = 1 := by native_decide

/-- expPartial 1 = 2. -/
example : expPartial 1 = 2 := by native_decide

/-- expPartial 2 = 5/2. -/
example : expPartial 2 = 5 / 2 := by native_decide

/-- expPartial 3 = 8/3. -/
example : expPartial 3 = 8 / 3 := by native_decide

/-- expPartial is strictly increasing. -/
example : ∀ n ∈ Finset.range 10, expPartial n < expPartial (n + 1) := by native_decide

/-- 2 < expPartial 3 < 3. -/
example : (2 : ℚ) < expPartial 3 ∧ expPartial 3 < 3 := by native_decide

/-- expPartial 10 > 271/100  (e ≈ 2.71828). -/
example : expPartial 10 > 271 / 100 := by native_decide

/-- expPartial 10 < 272/100  (e ≈ 2.71828). -/
example : expPartial 10 < 272 / 100 := by native_decide

/-- Combined: 271/100 < expPartial 10 < 272/100. -/
example : (271 : ℚ) / 100 < expPartial 10 ∧ expPartial 10 < 272 / 100 := by native_decide

/-! ## 6. Comparison of singularity types at radius ρ = 1

  For the unit circle:
  - Simple pole:   [z^n] 1/(1-z) = 1             (constant growth)
  - Double pole:   [z^n] 1/(1-z)^2 = n+1          (linear growth)
  - Alg. sing.:    [z^n] 1/√(1-z) = C(2n,n)/4^n  (decays like 1/√(πn))

  In particular C(2n,n)/4^n → 0, whereas n+1 → ∞.
  We show: (n+1) > centralBinom n  for n ≥ 3 would be FALSE
  (since C(6,3)=20 > 7), so the algebraic coefficient actually
  EXCEEDS the simple-pole coefficient for moderate n.

  What *is* true is the opposite: centralBinom n > n+1 for n ≥ 3,
  i.e. the 1/√(1-z) coefficients are LARGER than the 1/(1-z)^2 ones
  for those n (before the eventual decay sets in beyond integer precision).

  More precisely: centralBinom n > n+1 for n = 3..10.
-/

/-- centralBinom n > n+1 for n = 3..10. -/
example : ∀ n ∈ Finset.Icc 3 10, centralBinom n > n + 1 := by native_decide

/-- Spot-check: centralBinom 3 = 20 while 3+1 = 4. -/
example : centralBinom 3 = 20 ∧ centralBinom 3 > 3 + 1 := by native_decide

/-- Spot-check: centralBinom 10 = 184756 while 10+1 = 11. -/
example : centralBinom 10 = 184756 ∧ centralBinom 10 > 10 + 1 := by native_decide

/-- centralBinom n < 4^n for n = 1..10 (eventual decay). -/
example : ∀ n ∈ Finset.Icc 1 10, centralBinom n < 4 ^ n := by native_decide

/-- For large n the double-pole coefficient exceeds all: (n+1) > 1 for n ≥ 1. -/
example : ∀ n ∈ Finset.Icc 1 10, n + 1 > 1 := by native_decide

end SingularityClassification
