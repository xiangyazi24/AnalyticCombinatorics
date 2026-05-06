import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch4.RadiusOfConvergence


/-!
Radius of convergence and exponential growth rates, following the Chapter IV
dictionary of Analytic Combinatorics.

The analytic statements involving square roots, pi, e, singularities, and
limsup are recorded as named data.  The formal checks below are finite,
computable coefficient and ratio verifications, so every proof is discharged by
`native_decide`.
-/

/-! ## Analytic summaries -/

structure AnalyticSummary where
  family : String
  radius : String
  growthRate : String
  coefficientAsymptotic : String
deriving DecidableEq, Repr

def catalanSummary : AnalyticSummary :=
  { family := "Catalan numbers"
    radius := "R = 1/4"
    growthRate := "4^n"
    coefficientAsymptotic := "[z^n] C(z) ~ 4^n / (n^(3/2) * sqrt(pi))" }

def fibonacciSummary : AnalyticSummary :=
  { family := "Fibonacci numbers"
    radius := "R = (sqrt(5) - 1) / 2, approximately 0.618"
    growthRate := "phi^n, where phi = (1 + sqrt(5)) / 2"
    coefficientAsymptotic := "F_n = (phi^n - psi^n) / sqrt(5)" }

def motzkinSummary : AnalyticSummary :=
  { family := "Motzkin numbers"
    radius := "R = 1/3"
    growthRate := "3^n"
    coefficientAsymptotic := "M_n has dominant exponential factor 3^n" }

def derangementSummary : AnalyticSummary :=
  { family := "Derangements"
    radius := "R = 1 for the EGF, same dominant radius as exp(-1) / (1 - z)"
    growthRate := "n! / e"
    coefficientAsymptotic := "D_n ~ n! / e" }

def pringsheimTheorem : String :=
  "If f(z) = Sum a_n z^n has a_n >= 0, then its finite radius R is a singularity."

def hadamardFormula : String :=
  "Hadamard formula: 1 / R = limsup_n (a_n)^(1/n)."

inductive GrowthClass where
  | polynomialTimesExponential
  | subexponential
deriving DecidableEq, Repr

structure GrowthClassification where
  label : String
  kind : GrowthClass
deriving DecidableEq, Repr

def catalanGrowthClass : GrowthClassification :=
  { label := "Catalan: n^(-3/2) * 4^n"
    kind := GrowthClass.polynomialTimesExponential }

def fibonacciGrowthClass : GrowthClassification :=
  { label := "Fibonacci: constant * phi^n"
    kind := GrowthClass.polynomialTimesExponential }

def polynomialGrowthClass : GrowthClassification :=
  { label := "Pure polynomial growth"
    kind := GrowthClass.subexponential }

theorem catalan_classification :
    catalanGrowthClass.kind = GrowthClass.polynomialTimesExponential := by native_decide

theorem fibonacci_classification :
    fibonacciGrowthClass.kind = GrowthClass.polynomialTimesExponential := by native_decide

theorem polynomial_classification :
    polynomialGrowthClass.kind = GrowthClass.subexponential := by native_decide

/-! ## Catalan numbers: radius `1/4`, growth `4^n` -/

def catalanRadius : ℚ := 1 / 4

def catalanGrowthRate (n : ℕ) : ℕ := 4 ^ n

def centralBinomial (n : ℕ) : ℕ :=
  Nat.choose (2 * n) n

def catalanNumber (n : ℕ) : ℕ :=
  centralBinomial n / (n + 1)

def centralBinomialTable : Fin 13 → ℕ :=
  ![1, 2, 6, 20, 70, 252, 924, 3432, 12870, 48620, 184756, 705432, 2704156]

def catalanTable : Fin 13 → ℕ :=
  ![1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862, 16796, 58786, 208012]

def centralBinomialRatio (n : ℕ) : ℚ :=
  (centralBinomial n : ℚ) / (4 ^ n : ℚ)

def centralBinomialRatioTable : Fin 9 → ℚ :=
  ![(1 : ℚ), 1 / 2, 3 / 8, 5 / 16, 35 / 128, 63 / 256, 231 / 1024, 429 / 2048,
    6435 / 32768]

theorem catalan_radius_value : catalanRadius = 1 / 4 := by native_decide

theorem catalan_growth_values :
    ∀ n : Fin 10, catalanGrowthRate n.val = 4 ^ n.val := by native_decide

theorem central_binomial_table_checked :
    ∀ n : Fin 13, centralBinomial n.val = centralBinomialTable n := by native_decide

theorem catalan_table_checked :
    ∀ n : Fin 13, catalanNumber n.val = catalanTable n := by native_decide

theorem central_binomial_ratio_table_checked :
    ∀ n : Fin 9, centralBinomialRatio n.val = centralBinomialRatioTable n := by native_decide

theorem central_binomial_ratio_decreasing_checked :
    ∀ n : Fin 12, centralBinomialRatio (n.val + 1) ≤ centralBinomialRatio n.val := by
  native_decide

theorem central_binomial_basic_bound_checked :
    ∀ n : Fin 13, centralBinomial n.val ≤ 4 ^ n.val := by native_decide

theorem central_binomial_times_n_bound_true_until_three :
    ∀ n : Fin 3, centralBinomial (n.val + 1) * (n.val + 1) ≤ 4 ^ (n.val + 1) := by
  native_decide

theorem central_binomial_times_n_bound_fails_at_four :
    ¬ centralBinomial 4 * 4 ≤ 4 ^ 4 := by native_decide

/-! ## Fibonacci numbers: radius `(sqrt(5)-1)/2`, growth `phi^n` -/

def fibonacciRadiusApprox : ℚ := 618 / 1000

def phiApprox : ℚ := 1618 / 1000

def fibonacciTable : Fin 14 → ℕ :=
  ![0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233]

def fibonacciNumber (n : ℕ) : ℕ :=
  Nat.fib n

def fibonacciRatioNumDen : Fin 8 → ℕ × ℕ :=
  ![(8, 5), (13, 8), (21, 13), (34, 21), (55, 34), (89, 55), (144, 89),
    (233, 144)]

def fibonacciRatioTable : Fin 8 → ℚ :=
  ![(8 : ℚ) / 5, (13 : ℚ) / 8, (21 : ℚ) / 13, (34 : ℚ) / 21, (55 : ℚ) / 34,
    (89 : ℚ) / 55, (144 : ℚ) / 89, (233 : ℚ) / 144]

theorem fibonacci_radius_approx_value :
    fibonacciRadiusApprox = 618 / 1000 := by native_decide

theorem phi_approx_value :
    phiApprox = 1618 / 1000 := by native_decide

theorem fibonacci_table_checked :
    ∀ n : Fin 14, fibonacciNumber n.val = fibonacciTable n := by native_decide

theorem fibonacci_ratio_num_den_checked :
    ∀ n : Fin 8,
      fibonacciRatioNumDen n = (fibonacciNumber (n.val + 6), fibonacciNumber (n.val + 5)) := by
  native_decide

theorem fibonacci_ratio_table_checked :
    ∀ n : Fin 8,
      fibonacciRatioTable n =
        (fibonacciNumber (n.val + 6) : ℚ) / (fibonacciNumber (n.val + 5) : ℚ) := by
  native_decide

theorem fibonacci_ratios_alternate_around_phi_approx :
    fibonacciRatioTable 0 < phiApprox ∧
      phiApprox < fibonacciRatioTable 1 ∧
      fibonacciRatioTable 2 < phiApprox ∧
      phiApprox < fibonacciRatioTable 3 ∧
      fibonacciRatioTable 4 < phiApprox ∧
      phiApprox < fibonacciRatioTable 5 ∧
      fibonacciRatioTable 6 < phiApprox ∧
      phiApprox < fibonacciRatioTable 7 := by native_decide

/-! ## Motzkin numbers: radius `1/3`, growth `3^n` -/

def motzkinRadius : ℚ := 1 / 3

def motzkinGrowthRate (n : ℕ) : ℕ := 3 ^ n

def motzkinNumber : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 =>
      ((2 * n + 5) * motzkinNumber (n + 1) + (3 * n + 3) * motzkinNumber n) / (n + 4)

def motzkinTable : Fin 9 → ℕ :=
  ![1, 1, 2, 4, 9, 21, 51, 127, 323]

def motzkinRatioTable : Fin 8 → ℚ :=
  ![(1 : ℚ) / 3, (2 : ℚ) / 9, (4 : ℚ) / 27, (1 : ℚ) / 9, (7 : ℚ) / 81,
    (17 : ℚ) / 243, (127 : ℚ) / 2187, (323 : ℚ) / 6561]

def motzkinRatio (n : ℕ) : ℚ :=
  (motzkinNumber n : ℚ) / (3 ^ n : ℚ)

theorem motzkin_radius_value : motzkinRadius = 1 / 3 := by native_decide

theorem motzkin_growth_values :
    ∀ n : Fin 9, motzkinGrowthRate n.val = 3 ^ n.val := by native_decide

theorem motzkin_table_checked :
    ∀ n : Fin 9, motzkinNumber n.val = motzkinTable n := by native_decide

theorem motzkin_ratio_table_checked :
    ∀ n : Fin 8, motzkinRatio (n.val + 1) = motzkinRatioTable n := by native_decide

theorem motzkin_ratio_bounded_one_to_eight :
    ∀ n : Fin 8, 0 < motzkinRatio (n.val + 1) ∧ motzkinRatio (n.val + 1) ≤ 1 / 3 := by
  native_decide

/-! ## Derangements: EGF radius `1`, growth `n! / e` -/

def derangementRadius : ℚ := 1

def eApprox : ℚ := 271828 / 100000

def derangementNumber : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | n + 2 => (n + 1) * (derangementNumber (n + 1) + derangementNumber n)

def derangementTable : Fin 13 → ℕ :=
  ![1, 0, 1, 2, 9, 44, 265, 1854, 14833, 133496, 1334961, 14684570,
    176214841]

def absDiffNat (a b : ℕ) : ℕ :=
  if a ≤ b then b - a else a - b

def derangementFactorialGap (n : ℕ) : ℕ :=
  absDiffNat n.factorial (derangementNumber n + derangementNumber (n - 1))

def derangementFactorialGapTable : Fin 12 → ℕ :=
  ![0, 1, 3, 13, 67, 411, 2921, 23633, 214551, 2160343, 23897269, 288102189]

def derangementTimesEApproxScaledError (n : ℕ) : ℕ :=
  absDiffNat (derangementNumber n * 271828) (n.factorial * 100000)

def derangementTimesEApproxScaledErrorTable : Fin 9 → ℕ :=
  ![100000, 71828, 56344, 46452, 39568, 34420, 30888, 24724, 49312]

theorem derangement_radius_value : derangementRadius = 1 := by native_decide

theorem e_approx_value : eApprox = 271828 / 100000 := by native_decide

theorem derangement_table_checked :
    ∀ n : Fin 13, derangementNumber n.val = derangementTable n := by native_decide

theorem derangement_factorial_gap_table_checked :
    ∀ n : Fin 12, derangementFactorialGap (n.val + 1) = derangementFactorialGapTable n := by
  native_decide

theorem derangement_e_approx_scaled_error_checked :
    ∀ n : Fin 9,
      derangementTimesEApproxScaledError (n.val + 1) =
        derangementTimesEApproxScaledErrorTable n := by native_decide

theorem derangement_recurrence_checked :
    ∀ n : Fin 11,
      derangementNumber (n.val + 2) =
        (n.val + 1) * (derangementNumber (n.val + 1) + derangementNumber n.val) := by
  native_decide

/-! ## Hadamard formula: geometric verification -/

def geometricTwoCoeff (n : ℕ) : ℕ := 2 ^ n

def geometricTwoRadius : ℚ := 1 / 2

def geometricTwoInvRadius : ℕ := 2

def geometricTwoCoeffTable : Fin 10 → ℕ :=
  ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512]

theorem geometric_two_coeff_table_checked :
    ∀ n : Fin 10, geometricTwoCoeff n.val = geometricTwoCoeffTable n := by native_decide

theorem hadamard_geometric_two_radius :
    geometricTwoRadius = 1 / (geometricTwoInvRadius : ℚ) := by native_decide

theorem hadamard_geometric_two_growth :
    ∀ n : Fin 10, geometricTwoCoeff n.val = geometricTwoInvRadius ^ n.val := by native_decide



structure RadiusOfConvergenceBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RadiusOfConvergenceBudgetCertificate.controlled
    (c : RadiusOfConvergenceBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def RadiusOfConvergenceBudgetCertificate.budgetControlled
    (c : RadiusOfConvergenceBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def RadiusOfConvergenceBudgetCertificate.Ready
    (c : RadiusOfConvergenceBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RadiusOfConvergenceBudgetCertificate.size
    (c : RadiusOfConvergenceBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem radiusOfConvergence_budgetCertificate_le_size
    (c : RadiusOfConvergenceBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRadiusOfConvergenceBudgetCertificate :
    RadiusOfConvergenceBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleRadiusOfConvergenceBudgetCertificate.Ready := by
  constructor
  · norm_num [RadiusOfConvergenceBudgetCertificate.controlled,
      sampleRadiusOfConvergenceBudgetCertificate]
  · norm_num [RadiusOfConvergenceBudgetCertificate.budgetControlled,
      sampleRadiusOfConvergenceBudgetCertificate]

example :
    sampleRadiusOfConvergenceBudgetCertificate.certificateBudgetWindow ≤
      sampleRadiusOfConvergenceBudgetCertificate.size := by
  apply radiusOfConvergence_budgetCertificate_le_size
  constructor
  · norm_num [RadiusOfConvergenceBudgetCertificate.controlled,
      sampleRadiusOfConvergenceBudgetCertificate]
  · norm_num [RadiusOfConvergenceBudgetCertificate.budgetControlled,
      sampleRadiusOfConvergenceBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleRadiusOfConvergenceBudgetCertificate.Ready := by
  constructor
  · norm_num [RadiusOfConvergenceBudgetCertificate.controlled,
      sampleRadiusOfConvergenceBudgetCertificate]
  · norm_num [RadiusOfConvergenceBudgetCertificate.budgetControlled,
      sampleRadiusOfConvergenceBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRadiusOfConvergenceBudgetCertificate.certificateBudgetWindow ≤
      sampleRadiusOfConvergenceBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List RadiusOfConvergenceBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRadiusOfConvergenceBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleRadiusOfConvergenceBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch4.RadiusOfConvergence
