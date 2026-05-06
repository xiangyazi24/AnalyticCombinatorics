import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch4.AsymptoticSeries


/-!
  Chapter IV computational checks for asymptotic series and expansions.

  The analytic statements are represented by exact integer or rational
  checkable proxies.  This keeps every proof in the file decidable by
  `native_decide`.
-/

/-! ## 1. Stirling series structure and factorial growth

  Stirling's leading scale is
    n! ~ sqrt(2*pi*n) * (n/e)^n.

  The correction series starts
    1 + 1/(12n) + 1/(288n^2) - 139/(51840n^3) - ...
-/

/-- A finite encoded prefix of a Stirling-type asymptotic series. -/
structure StirlingSeries where
  leadingScale : String
  correctionNumerators : List ℤ
  correctionDenominators : List ℕ
deriving DecidableEq, Repr

/-- Stirling series prefix for `n!`. -/
def stirlingFactorialSeries : StirlingSeries where
  leadingScale := "sqrt(2*pi*n) * (n/e)^n"
  correctionNumerators := [1, 1, 1, -139, -571]
  correctionDenominators := [1, 12, 288, 51840, 2488320]

example : stirlingFactorialSeries.correctionNumerators.length = 5 := by native_decide
example : stirlingFactorialSeries.correctionDenominators.length = 5 := by native_decide
example : stirlingFactorialSeries.correctionDenominators[1]! = 12 := by native_decide
example : stirlingFactorialSeries.correctionNumerators[3]! = -139 := by native_decide

/-- Factorial values eventually dominate fixed exponential samples. -/
example : Nat.factorial 8 > 2 ^ 8 := by native_decide
example : Nat.factorial 10 > 3 ^ 10 := by native_decide
example : Nat.factorial 12 > 4 ^ 12 := by native_decide
example : Nat.factorial 15 > 10 ^ 10 := by native_decide
example : Nat.factorial 20 > 10 ^ 17 := by native_decide

/-- Consecutive factorial ratios, in integer form. -/
example : Nat.factorial 6 = 6 * Nat.factorial 5 := by native_decide
example : Nat.factorial 10 = 10 * Nat.factorial 9 := by native_decide
example : Nat.factorial 15 = 15 * Nat.factorial 14 := by native_decide

/-! ## 2. Harmonic numbers scaled by factorials

  `harmonicFactorial n` is the integer quantity `H_n * n!`.
-/

/-- Rational harmonic number `H_n = sum_{k=1}^n 1/k`. -/
def harmonicRat (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range n, 1 / ((k + 1 : ℕ) : ℚ)

/-- Integer-scaled harmonic number `H_n * n!`. -/
def harmonicFactorial (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n, Nat.factorial n / (k + 1)

example : harmonicRat 1 = 1 := by native_decide
example : harmonicRat 5 = 137 / 60 := by native_decide
example : harmonicRat 10 = 7381 / 2520 := by native_decide

example : harmonicFactorial 1 = 1 := by native_decide
example : harmonicFactorial 2 = 3 := by native_decide
example : harmonicFactorial 3 = 11 := by native_decide
example : harmonicFactorial 4 = 50 := by native_decide
example : harmonicFactorial 5 = 274 := by native_decide
example : harmonicFactorial 6 = 1764 := by native_decide

/-- Small checks comparing `H_n * n!` with `(n+1)!`. -/
example : harmonicFactorial 1 < Nat.factorial 2 := by native_decide
example : harmonicFactorial 2 < Nat.factorial 3 := by native_decide
example : harmonicFactorial 3 < Nat.factorial 4 := by native_decide
example : harmonicFactorial 4 < Nat.factorial 5 := by native_decide
example : harmonicFactorial 5 < Nat.factorial 6 := by native_decide
example : harmonicFactorial 6 < Nat.factorial 7 := by native_decide

/-! ## 3. Euler-Maclaurin power-sum approximations

  For `p = 1, 2, 3`, the following exact formulas are the polynomial
  approximants that Euler-Maclaurin recovers.
-/

/-- Power sum `sum_{k=1}^n k^p`. -/
def powerSum (p n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n, (k + 1) ^ p

/-- Integral-scale upper and lower bounds for `sum_{k=1}^n k^p`. -/
def powerSumIntegralBounds (p n : ℕ) : Bool :=
  n ^ (p + 1) <= (p + 1) * powerSum p n &&
    (p + 1) * powerSum p n <= (n + 1) ^ (p + 1)

example : 2 * powerSum 1 10 = 10 * 11 := by native_decide
example : 2 * powerSum 1 20 = 20 * 21 := by native_decide

example : 6 * powerSum 2 10 = 10 * 11 * 21 := by native_decide
example : 6 * powerSum 2 12 = 12 * 13 * 25 := by native_decide

example : 4 * powerSum 3 8 = (8 * 9) ^ 2 := by native_decide
example : 4 * powerSum 3 10 = (10 * 11) ^ 2 := by native_decide

example : powerSumIntegralBounds 1 5 = true := by native_decide
example : powerSumIntegralBounds 1 10 = true := by native_decide
example : powerSumIntegralBounds 2 5 = true := by native_decide
example : powerSumIntegralBounds 2 10 = true := by native_decide
example : powerSumIntegralBounds 3 5 = true := by native_decide
example : powerSumIntegralBounds 3 10 = true := by native_decide

/-! ## 4. Central binomial asymptotics

  The expansion `C(2n,n) ~ 4^n / sqrt(pi*n)` implies sub-`4^n`
  growth with a square-root correction.  The checks below use integer
  inequalities and the exact central-binomial recurrence.
-/

/-- Central binomial coefficient `C(2n,n)`. -/
def centralBinomial (n : ℕ) : ℕ :=
  Nat.choose (2 * n) n

example : centralBinomial 1 = 2 := by native_decide
example : centralBinomial 2 = 6 := by native_decide
example : centralBinomial 3 = 20 := by native_decide
example : centralBinomial 4 = 70 := by native_decide
example : centralBinomial 8 = 12870 := by native_decide
example : centralBinomial 10 = 184756 := by native_decide

example : centralBinomial 3 < 4 ^ 3 := by native_decide
example : centralBinomial 5 < 4 ^ 5 := by native_decide
example : centralBinomial 8 < 4 ^ 8 := by native_decide
example : centralBinomial 10 < 4 ^ 10 := by native_decide

example : centralBinomial 3 * (2 * 3 + 1) > 4 ^ 3 := by native_decide
example : centralBinomial 5 * (2 * 5 + 1) > 4 ^ 5 := by native_decide
example : centralBinomial 8 * (2 * 8 + 1) > 4 ^ 8 := by native_decide
example : centralBinomial 10 * (2 * 10 + 1) > 4 ^ 10 := by native_decide

example : centralBinomial 2 * 2 = centralBinomial 1 * (4 * 1 + 2) := by native_decide
example : centralBinomial 3 * 3 = centralBinomial 2 * (4 * 2 + 2) := by native_decide
example : centralBinomial 4 * 4 = centralBinomial 3 * (4 * 3 + 2) := by native_decide
example : centralBinomial 5 * 5 = centralBinomial 4 * (4 * 4 + 2) := by native_decide

/-! ## 5. Beta function at integer arguments

  For positive integers, `Gamma n = (n-1)!`, so
    B(a,b) = Gamma(a) * Gamma(b) / Gamma(a+b).
-/

/-- Integer Gamma values, with `Gamma(n) = (n-1)!` for positive `n`. -/
def gammaInt (n : ℕ) : ℕ :=
  if n = 0 then 0 else Nat.factorial (n - 1)

/-- Beta value computed from integer Gamma values. -/
def betaByGamma (a b : ℕ) : ℚ :=
  (gammaInt a : ℚ) * (gammaInt b : ℚ) / (gammaInt (a + b) : ℚ)

/-- The factorial form of `B(a,b)` for positive integers. -/
def betaIntegerFormula (a b : ℕ) : ℚ :=
  (Nat.factorial (a - 1) : ℚ) * (Nat.factorial (b - 1) : ℚ) /
    (Nat.factorial (a + b - 1) : ℚ)

example : gammaInt 1 = 1 := by native_decide
example : gammaInt 2 = 1 := by native_decide
example : gammaInt 5 = 24 := by native_decide

example : betaByGamma 1 1 = 1 := by native_decide
example : betaByGamma 2 2 = 1 / 6 := by native_decide
example : betaByGamma 2 3 = 1 / 12 := by native_decide
example : betaByGamma 3 4 = 1 / 60 := by native_decide
example : betaByGamma 4 5 = 1 / 280 := by native_decide

example : betaByGamma 2 3 = betaIntegerFormula 2 3 := by native_decide
example : betaByGamma 3 4 = betaIntegerFormula 3 4 := by native_decide
example : betaByGamma 4 5 = betaIntegerFormula 4 5 := by native_decide

/-! ## 6. Laplace method motivation

  The Gamma integral gives
    integral_0^infty x^n * exp(-x) dx = Gamma(n+1) = n!.

  We record the exact integer moments and the integration-by-parts
  recurrence in the decidable integer model.
-/

/-- Integer value of the Gamma/Laplace moment `int x^n e^{-x} dx`. -/
def laplaceMoment (n : ℕ) : ℕ :=
  Nat.factorial n

example : laplaceMoment 0 = 1 := by native_decide
example : laplaceMoment 1 = 1 := by native_decide
example : laplaceMoment 2 = 2 := by native_decide
example : laplaceMoment 3 = 6 := by native_decide
example : laplaceMoment 5 = 120 := by native_decide
example : laplaceMoment 8 = 40320 := by native_decide

example : laplaceMoment 2 = 2 * laplaceMoment 1 := by native_decide
example : laplaceMoment 3 = 3 * laplaceMoment 2 := by native_decide
example : laplaceMoment 4 = 4 * laplaceMoment 3 := by native_decide
example : laplaceMoment 6 = 6 * laplaceMoment 5 := by native_decide
example : laplaceMoment 10 = 10 * laplaceMoment 9 := by native_decide

/-- Stirling correction numerator sample. -/
theorem stirlingFactorialSeries_numerator_three :
    stirlingFactorialSeries.correctionNumerators[3]! = -139 := by
  native_decide

/-- Central-binomial sample used in the asymptotic scale checks. -/
theorem centralBinomial_ten :
    centralBinomial 10 = 184756 := by
  native_decide



structure AsymptoticSeriesBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AsymptoticSeriesBudgetCertificate.controlled
    (c : AsymptoticSeriesBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AsymptoticSeriesBudgetCertificate.budgetControlled
    (c : AsymptoticSeriesBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AsymptoticSeriesBudgetCertificate.Ready
    (c : AsymptoticSeriesBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AsymptoticSeriesBudgetCertificate.size
    (c : AsymptoticSeriesBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem asymptoticSeries_budgetCertificate_le_size
    (c : AsymptoticSeriesBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAsymptoticSeriesBudgetCertificate :
    AsymptoticSeriesBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleAsymptoticSeriesBudgetCertificate.Ready := by
  constructor
  · norm_num [AsymptoticSeriesBudgetCertificate.controlled,
      sampleAsymptoticSeriesBudgetCertificate]
  · norm_num [AsymptoticSeriesBudgetCertificate.budgetControlled,
      sampleAsymptoticSeriesBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAsymptoticSeriesBudgetCertificate.certificateBudgetWindow ≤
      sampleAsymptoticSeriesBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleAsymptoticSeriesBudgetCertificate.Ready := by
  constructor
  · norm_num [AsymptoticSeriesBudgetCertificate.controlled,
      sampleAsymptoticSeriesBudgetCertificate]
  · norm_num [AsymptoticSeriesBudgetCertificate.budgetControlled,
      sampleAsymptoticSeriesBudgetCertificate]

example :
    sampleAsymptoticSeriesBudgetCertificate.certificateBudgetWindow ≤
      sampleAsymptoticSeriesBudgetCertificate.size := by
  apply asymptoticSeries_budgetCertificate_le_size
  constructor
  · norm_num [AsymptoticSeriesBudgetCertificate.controlled,
      sampleAsymptoticSeriesBudgetCertificate]
  · norm_num [AsymptoticSeriesBudgetCertificate.budgetControlled,
      sampleAsymptoticSeriesBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List AsymptoticSeriesBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAsymptoticSeriesBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleAsymptoticSeriesBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch4.AsymptoticSeries
