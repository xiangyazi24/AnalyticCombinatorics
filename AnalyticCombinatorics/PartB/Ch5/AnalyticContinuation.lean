import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch5.AnalyticContinuation


open Finset

/-!
  Analytic continuation and meromorphic functions, in the computational
  spirit of Chapter V of Flajolet and Sedgewick.

  The analytic assertions below are represented as finite arithmetic
  certificates: rational tables, cross-multiplied identities, and certified
  partial-sum bounds.  This keeps every proof decidable by `native_decide`.
-/

/-! ## 1. Geometric sums and meromorphic continuation of `1 / (1 - z)` -/

/-- Integer partial sums `sum_{k=0}^n r^k`. -/
def geometricPartialSumInt (r : ℤ) (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), r ^ k

/-- Natural-number partial sums `sum_{k=0}^n r^k`. -/
def geometricPartialSumNat (r : ℕ) (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), r ^ k

/-- Integer ratios used to check the closed form away from the pole `r = 1`. -/
def integerRatioTable : Fin 9 → ℤ :=
  ![-3, -2, -1, 0, 2, 3, 4, 5, 10]

/--
Finite integer checks of
`sum_{k=0}^n r^k = (r^(n+1) - 1) / (r - 1)` for `r != 1`.
-/
theorem geometric_series_integer_closed_form_checked :
    ∀ i : Fin 9, ∀ n : Fin 11,
      geometricPartialSumInt (integerRatioTable i) n.val =
        ((integerRatioTable i) ^ (n.val + 1) - 1) / ((integerRatioTable i) - 1) ∧
      ((integerRatioTable i) - 1) * geometricPartialSumInt (integerRatioTable i) n.val =
        (integerRatioTable i) ^ (n.val + 1) - 1 := by
  native_decide

/-- Values of `sum_{k=0}^n 2^k` for `0 <= n <= 10`. -/
def twoPowerGeometricSumTable : Fin 11 → ℕ :=
  ![1, 3, 7, 15, 31, 63, 127, 255, 511, 1023, 2047]

theorem two_power_geometric_sum_values_0_to_10 :
    ∀ n : Fin 11,
      geometricPartialSumNat 2 n.val = twoPowerGeometricSumTable n ∧
      geometricPartialSumNat 2 n.val = 2 ^ (n.val + 1) - 1 := by
  native_decide

/-! ## 2. Bernoulli numbers and trivial zeros of zeta -/

/-- Numerator of the Bernoulli number `B_n`, using the convention `B_1 = -1/2`. -/
def bernoulliNumerator : ℕ → ℤ
  | 0 => 1
  | 1 => -1
  | 2 => 1
  | 4 => -1
  | 6 => 1
  | 8 => -1
  | 10 => 5
  | 12 => -691
  | _ => 0

/-- Positive denominator of the Bernoulli number `B_n`. -/
def bernoulliDenominator : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | 2 => 6
  | 4 => 30
  | 6 => 42
  | 8 => 30
  | 10 => 66
  | 12 => 2730
  | _ => 1

/-- Bernoulli numbers as exact rationals. -/
def bernoulliNumber (n : ℕ) : ℚ :=
  (bernoulliNumerator n : ℚ) / (bernoulliDenominator n : ℚ)

theorem bernoulli_initial_values :
    bernoulliNumber 0 = 1 ∧
      bernoulliNumber 1 = (-1 : ℚ) / 2 ∧
      bernoulliNumber 2 = (1 : ℚ) / 6 ∧
      bernoulliNumber 4 = (-1 : ℚ) / 30 ∧
      bernoulliNumber 6 = (1 : ℚ) / 42 := by
  native_decide

/-- Numerators of `B_{2k}` for `0 <= k <= 6`. -/
def bernoulliEvenNumeratorTable : Fin 7 → ℤ :=
  ![1, 1, -1, 1, -1, 5, -691]

/-- Denominators of `B_{2k}` for `0 <= k <= 6`. -/
def bernoulliEvenDenominatorTable : Fin 7 → ℕ :=
  ![1, 6, 30, 42, 30, 66, 2730]

theorem bernoulli_even_numerator_denominator_pairs_0_to_6 :
    ∀ k : Fin 7,
      bernoulliNumerator (2 * k.val) = bernoulliEvenNumeratorTable k ∧
      bernoulliDenominator (2 * k.val) = bernoulliEvenDenominatorTable k ∧
      bernoulliNumber (2 * k.val) =
        (bernoulliEvenNumeratorTable k : ℚ) /
          (bernoulliEvenDenominatorTable k : ℚ) := by
  native_decide

/--
Rational certificate for the analytically continued zeta value
`zeta(-n) = (-1)^n B_{n+1} / (n+1)`.
-/
def zetaNegativeIntegerValue (n : ℕ) : ℚ :=
  (-1 : ℚ) ^ n * bernoulliNumber (n + 1) / (n + 1 : ℚ)

/-- The even-negative specialization `zeta(-2k)`. -/
def zetaNegativeEvenValue (k : ℕ) : ℚ :=
  zetaNegativeIntegerValue (2 * k)

theorem zeta_negative_even_trivial_zeros_via_bernoulli :
    ∀ k : Fin 7, 1 ≤ k.val →
      zetaNegativeEvenValue k.val = 0 ∧
      bernoulliNumber (2 * k.val + 1) = 0 ∧
      zetaNegativeEvenValue k.val =
        bernoulliNumber (2 * k.val + 1) / (2 * k.val + 1 : ℚ) := by
  native_decide

/-! ## 3. The positive even zeta value `zeta(2) = pi^2 / 6` -/

/-- Exact rational partial sum `sum_{k=1}^n 1/k^2`. -/
def reciprocalSquarePartialSum (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range n, (1 : ℚ) / ((k + 1) ^ 2 : ℚ)

/-- Decimal rational certificate for `pi^2 / 6`. -/
def piSquaredOverSixCertificate : ℚ :=
  1644934068 / 1000000000

/-- Partial-sum lengths used for bounding the `zeta(2)` certificate. -/
def zetaTwoPartialLengthTable : Fin 4 → ℕ :=
  ![10, 20, 50, 100]

/--
The integral-test tail bound
`sum_{k=1}^n 1/k^2 < pi^2/6 < sum_{k=1}^n 1/k^2 + 1/n`
for the tabulated partial sums.
-/
theorem zeta_two_pi_squared_over_six_partial_sum_bounds :
    ∀ i : Fin 4,
      let n := zetaTwoPartialLengthTable i
      reciprocalSquarePartialSum n < piSquaredOverSixCertificate ∧
      piSquaredOverSixCertificate < reciprocalSquarePartialSum n + (1 : ℚ) / n := by
  native_decide

/-! ## 4. Harmonic sums and logarithmic singularities -/

/-- Exact rational harmonic numbers `H_n = sum_{k=1}^n 1/k`. -/
def harmonicNumber : ℕ → ℚ
  | 0 => 0
  | n + 1 => harmonicNumber n + (1 : ℚ) / (n + 1 : ℚ)

/-- Reduced numerators of `H_n` for `0 <= n <= 12`. -/
def harmonicNumeratorTable : Fin 13 → ℕ :=
  ![0, 1, 3, 11, 25, 137, 49, 363, 761, 7129, 7381, 83711, 86021]

/-- Reduced denominators of `H_n` for `0 <= n <= 12`. -/
def harmonicDenominatorTable : Fin 13 → ℕ :=
  ![1, 1, 2, 6, 12, 60, 20, 140, 280, 2520, 2520, 27720, 27720]

theorem harmonic_sum_exact_numerator_denominator_pairs :
    ∀ n : Fin 13,
      harmonicNumber n.val =
        (harmonicNumeratorTable n : ℚ) / (harmonicDenominatorTable n : ℚ) := by
  native_decide

/-! ## 5. Euler-Mascheroni approximation certificates -/

/-- Scaling factor for the tabulated natural-logarithm floors. -/
def logScale : ℕ := 1000000

/-- `floor(logScale * log n)` for `0 <= n <= 12`, with the `0` slot unused. -/
def lnScaledFloorTable : Fin 13 → ℕ :=
  ![0, 0, 693147, 1098612, 1386294, 1609437, 1791759,
    1945910, 2079441, 2197224, 2302585, 2397895, 2484906]

/--
Numerator of `H_n - floor(logScale * log n) / logScale`, using the exact
denominator `harmonicDenominatorTable n * logScale`.
-/
def eulerMascheroniScaledNumerator (n : Fin 13) : ℕ :=
  logScale * harmonicNumeratorTable n - harmonicDenominatorTable n * lnScaledFloorTable n

/-- Denominator paired with `eulerMascheroniScaledNumerator`. -/
def eulerMascheroniScaledDenominator (n : Fin 13) : ℕ :=
  harmonicDenominatorTable n * logScale

theorem euler_mascheroni_scaled_numerator_bounds_8_to_12 :
    ∀ n : Fin 13, 8 ≤ n.val →
      57 * eulerMascheroniScaledDenominator n <
        100 * eulerMascheroniScaledNumerator n ∧
      100 * eulerMascheroniScaledNumerator n <
        65 * eulerMascheroniScaledDenominator n := by
  native_decide



structure AnalyticContinuationBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AnalyticContinuationBudgetCertificate.controlled
    (c : AnalyticContinuationBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AnalyticContinuationBudgetCertificate.budgetControlled
    (c : AnalyticContinuationBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AnalyticContinuationBudgetCertificate.Ready
    (c : AnalyticContinuationBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AnalyticContinuationBudgetCertificate.size
    (c : AnalyticContinuationBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem analyticContinuation_budgetCertificate_le_size
    (c : AnalyticContinuationBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAnalyticContinuationBudgetCertificate :
    AnalyticContinuationBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleAnalyticContinuationBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticContinuationBudgetCertificate.controlled,
      sampleAnalyticContinuationBudgetCertificate]
  · norm_num [AnalyticContinuationBudgetCertificate.budgetControlled,
      sampleAnalyticContinuationBudgetCertificate]

example :
    sampleAnalyticContinuationBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticContinuationBudgetCertificate.size := by
  apply analyticContinuation_budgetCertificate_le_size
  constructor
  · norm_num [AnalyticContinuationBudgetCertificate.controlled,
      sampleAnalyticContinuationBudgetCertificate]
  · norm_num [AnalyticContinuationBudgetCertificate.budgetControlled,
      sampleAnalyticContinuationBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleAnalyticContinuationBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticContinuationBudgetCertificate.controlled,
      sampleAnalyticContinuationBudgetCertificate]
  · norm_num [AnalyticContinuationBudgetCertificate.budgetControlled,
      sampleAnalyticContinuationBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAnalyticContinuationBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticContinuationBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List AnalyticContinuationBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAnalyticContinuationBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleAnalyticContinuationBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch5.AnalyticContinuation
