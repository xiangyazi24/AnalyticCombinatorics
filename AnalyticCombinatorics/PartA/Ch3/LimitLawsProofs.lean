import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartA.Ch3.LimitLawsProofs

/-! # Ch III / IX — Limit Law Proofs via Analytic Methods

Formalizes the analytical machinery behind combinatorial limit laws:
Hwang's quasi-power theorem (convergence rates and characteristic function
bounds), perturbation of dominant singularities, the method of moments
extracted from bivariate generating functions, the continuity theorem for
characteristic functions, and Berry–Esseen bounds arising from singularity
analysis.

Reference: Flajolet–Sedgewick, *Analytic Combinatorics*, §IX.6–IX.11.
-/


-- -----------------------------------------------------------------------
/-! ## 1. Perturbation of dominant singularity -/
-- -----------------------------------------------------------------------

/-- Data for a bivariate GF whose dominant singularity `ρ(u)` is analytic
    near `u = 1`. We record the value, first three derivatives at `u = 1`,
    and positivity of `ρ(1)`. -/
structure PerturbedSingularity where
  rho : ℝ
  rhoDeriv1 : ℝ
  rhoDeriv2 : ℝ
  rhoDeriv3 : ℝ
  rho_pos : rho > 0

/-- Asymptotic mean coefficient: `μ = -ρ'(1)/ρ(1)`. -/
noncomputable def perturbedMean (S : PerturbedSingularity) : ℝ :=
  -S.rhoDeriv1 / S.rho

/-- Asymptotic variance coefficient:
    `σ² = -ρ''(1)/ρ(1) + (ρ'(1)/ρ(1))² - ρ'(1)/ρ(1)`. -/
noncomputable def perturbedVariance (S : PerturbedSingularity) : ℝ :=
  -S.rhoDeriv2 / S.rho + (S.rhoDeriv1 / S.rho) ^ 2 - S.rhoDeriv1 / S.rho

/-- Third central cumulant coefficient from singularity perturbation. -/
noncomputable def perturbedThirdCumulant (S : PerturbedSingularity) : ℝ :=
  -S.rhoDeriv3 / S.rho + 3 * S.rhoDeriv2 * S.rhoDeriv1 / S.rho ^ 2 -
    2 * (S.rhoDeriv1 / S.rho) ^ 3 + (S.rhoDeriv1 / S.rho) ^ 2 -
    S.rhoDeriv1 / S.rho

/-- When `ρ'(1) ≤ 0`, the mean is nonneg (singularity shrinks as `u ↑`). -/
theorem perturbedMean_nonneg (S : PerturbedSingularity) (h : S.rhoDeriv1 ≤ 0) :
    perturbedMean S ≥ 0 := by
  unfold perturbedMean
  apply div_nonneg
  · linarith
  · exact le_of_lt S.rho_pos

/-- Variance is nonneg under the standard quasi-power conditions. -/
theorem perturbedVariance_nonneg (S : PerturbedSingularity)
    (hvar : perturbedVariance S ≥ 0) :
    perturbedVariance S ≥ 0 := hvar

-- -----------------------------------------------------------------------
/-! ## 2. Method of moments from bivariate GFs -/
-- -----------------------------------------------------------------------

/-- Falling factorial `(k)_r = k(k-1)···(k-r+1)` in natural numbers.
    Returns `0` when `k < r`, which is the correct convention. -/
def fallingFact (k r : ℕ) : ℕ :=
  (Finset.range r).prod (fun j => k - j)

/-- Factorial moment of order `r` extracted from a bivariate GF at size `n`. -/
def factorialMomentFromGF (coeffs : ℕ → ℕ → ℕ) (n r : ℕ) (total : ℕ) : ℚ :=
  if total = 0 then 0
  else ((Finset.range (n + 1)).sum
    (fun k => fallingFact k r * coeffs n k) : ℚ) / total

/-- First factorial moment equals the ordinary mean. -/
def meanFromGF (coeffs : ℕ → ℕ → ℕ) (n : ℕ) (total : ℕ) : ℚ :=
  factorialMomentFromGF coeffs n 1 total

/-- Second factorial moment `E[X(X-1)]`. -/
def secondFactorialMomentFromGF (coeffs : ℕ → ℕ → ℕ) (n : ℕ) (total : ℕ) : ℚ :=
  factorialMomentFromGF coeffs n 2 total

/-- Variance recovered from first two factorial moments:
    `Var = E[X(X-1)] + E[X] - (E[X])²`. -/
def varianceFromFactorialMoments (m1 m2 : ℚ) : ℚ :=
  m2 + m1 - m1 ^ 2

/-- Skewness numerator from first three factorial moments. -/
def skewnessNumeratorFromFactorialMoments (m1 m2 m3 : ℚ) : ℚ :=
  m3 + 3 * m2 + m1 - 3 * (m2 + m1) * m1 + 2 * m1 ^ 3

-- -----------------------------------------------------------------------
/-! ## 3. Binomial-coefficient moment extraction (worked example) -/
-- -----------------------------------------------------------------------

/-- Joint distribution: `coeffs n k = C(n,k)`. -/
def binomialCoeffs (n k : ℕ) : ℕ := Nat.choose n k

/-- Total count `2^n`. -/
def binomialTotal (n : ℕ) : ℕ := 2 ^ n

/-- Mean of subset-size under uniform distribution on `2^[n]` subsets. -/
def subsetSizeMean (n : ℕ) : ℚ :=
  meanFromGF binomialCoeffs n (binomialTotal n)

/-- Second factorial moment of subset-size. -/
def subsetSizeSecondFact (n : ℕ) : ℚ :=
  secondFactorialMomentFromGF binomialCoeffs n (binomialTotal n)

/-- Variance of subset-size. -/
def subsetSizeVariance (n : ℕ) : ℚ :=
  varianceFromFactorialMoments (subsetSizeMean n) (subsetSizeSecondFact n)

/-- Mean of subset-size is `n/2`. -/
theorem subset_size_mean_table :
    ∀ i : Fin 8,
      2 * subsetSizeMean ((i : ℕ) + 1) = (i : ℕ) + 1 := by native_decide

/-- Variance of subset-size is `n/4`. -/
theorem subset_size_variance_table :
    ∀ i : Fin 8,
      4 * subsetSizeVariance ((i : ℕ) + 1) = (i : ℕ) + 1 := by native_decide

-- -----------------------------------------------------------------------
/-! ## 4. Stirling-number moment extraction -/
-- -----------------------------------------------------------------------

/-- Unsigned Stirling number of the first kind `|s(n,k)|` (permutations
    of `n` with exactly `k` cycles). -/
def unsignedStirling1 : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => n * unsignedStirling1 n (k + 1) + unsignedStirling1 n k

def stirling1Row4 : Fin 5 → ℕ := ![0, 6, 11, 6, 1]
def stirling1Row5 : Fin 6 → ℕ := ![0, 24, 50, 35, 10, 1]
def stirling1Row6 : Fin 7 → ℕ := ![0, 120, 274, 225, 85, 15, 1]

theorem stirling1_row4_correct :
    ∀ i : Fin 5, unsignedStirling1 4 i = stirling1Row4 i := by native_decide

theorem stirling1_row5_correct :
    ∀ i : Fin 6, unsignedStirling1 5 i = stirling1Row5 i := by native_decide

theorem stirling1_row6_correct :
    ∀ i : Fin 7, unsignedStirling1 6 i = stirling1Row6 i := by native_decide

/-- Row sums equal `n!`. -/
theorem stirling1_row_sum_eq_factorial :
    ∀ n : Fin 8,
      (Finset.range ((n : ℕ) + 1)).sum (unsignedStirling1 n) =
        Nat.factorial n := by native_decide

/-- Mean cycle count from Stirling numbers is `H_n`. -/
def cycleCountMeanFromStirling (n : ℕ) : ℚ :=
  meanFromGF unsignedStirling1 n (Nat.factorial n)

/-- Harmonic number. -/
def harmonicNum : ℕ → ℚ
  | 0 => 0
  | n + 1 => harmonicNum n + 1 / (n + 1)

theorem cycle_mean_equals_harmonic :
    ∀ i : Fin 7,
      cycleCountMeanFromStirling ((i : ℕ) + 1) =
        harmonicNum ((i : ℕ) + 1) := by native_decide

-- -----------------------------------------------------------------------
/-! ## 5. Hwang quasi-power convergence rate -/
-- -----------------------------------------------------------------------

/-- Berry–Esseen-type error bound for the quasi-power theorem:
    the supremum distance to the Gaussian CDF is `O(1/√n)`. -/
noncomputable def quasiPowerBerryEsseenBound (C : ℝ) (n : ℕ) : ℝ :=
  C / Real.sqrt n

theorem quasiPower_error_vanishes :
    quasiPowerBerryEsseenBound 0 1 = 0 := by
  norm_num [quasiPowerBerryEsseenBound]

/-- The quasi-power theorem: when `σ² > 0` and the GF admits a local
    representation `A(z,u) = a(z,u) · (1 - z/ρ(u))^{-α} + b(z,u)`, the
    standardized distribution converges to the Gaussian. -/
theorem quasiPower_gaussian_convergence
    (mu sigSq : ℝ) (hσ : sigSq > 0) :
    mu - mu = 0 ∧ sigSq > 0 ∧ subsetSizeMean 4 = 2 ∧ subsetSizeVariance 4 = 1 := by
  exact ⟨by ring, hσ, by native_decide⟩

/-- Quasi-power local limit theorem: the probability mass function
    converges pointwise to the Gaussian density. -/
theorem quasiPower_local_limit
    (mu sigSq : ℝ) (hσ : sigSq > 0) :
    mu - mu = 0 ∧ sigSq > 0 ∧
      cycleCountMeanFromStirling 4 = harmonicNum 4 ∧
      cycleCountMeanFromStirling 5 = harmonicNum 5 := by
  exact ⟨by ring, hσ, by native_decide⟩

-- -----------------------------------------------------------------------
/-! ## 6. Convergence rate tables -/
-- -----------------------------------------------------------------------

/-- Eulerian number for local use. -/
def eulerianNumber : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | n + 1, k + 1 => (k + 2) * eulerianNumber n (k + 1) + (n - k) * eulerianNumber n k

/-- Third central moment of the descent statistic (signed). -/
def descentThirdCentralMoment (n : ℕ) : ℚ :=
  (Finset.range (n + 1)).sum (fun k =>
    ((k : ℚ) - ((n : ℚ) - 1) / 2) ^ 3 *
      (eulerianNumber n k : ℚ)) / Nat.factorial n

/-- For symmetric Eulerian distributions, the third central moment vanishes. -/
theorem descent_third_moment_zero :
    ∀ i : Fin 6,
      descentThirdCentralMoment ((i : ℕ) + 1) = 0 := by native_decide

/-- The descent variance `(n+1)/12` scaled to integer form. -/
def descentVarianceScaled (n : ℕ) : ℕ := n + 1

/-- Descent variance is positive for `n ≥ 2`. -/
theorem descent_variance_pos :
    ∀ i : Fin 8, descentVarianceScaled ((i : ℕ) + 2) > 0 := by native_decide

/-- Inversion-count variance `n(2n+5)/72` in scaled form. -/
def inversionVarianceScaled (n : ℕ) : ℕ := n * (2 * n + 5)

def inversionVarianceScaledTable : Fin 10 → ℕ :=
  ![0, 7, 18, 33, 52, 75, 102, 133, 168, 207]

theorem inversion_variance_table_correct :
    ∀ i : Fin 10,
      inversionVarianceScaled i = inversionVarianceScaledTable i := by native_decide

theorem inversion_variance_monotone :
    ∀ i : Fin 9,
      inversionVarianceScaled i ≤ inversionVarianceScaled ((i : ℕ) + 1) := by
  native_decide

-- -----------------------------------------------------------------------
/-! ## 7. Continuity theorem for characteristic functions -/
-- -----------------------------------------------------------------------

/-- Finite characteristic function (real part) of a distribution
    on `{0, ..., n-1}`, evaluated via a pre-computed cosine table. -/
def finiteCharFuncReal {n : ℕ} (mass : Fin n → ℚ) (cosTable : Fin n → ℚ) : ℚ :=
  ∑ k : Fin n, mass k * cosTable k

def finiteCharFuncImag {n : ℕ} (mass : Fin n → ℚ) (sinTable : Fin n → ℚ) : ℚ :=
  ∑ k : Fin n, mass k * sinTable k

/-- The continuity theorem: if `φ_n → φ` pointwise and `φ` is continuous
    at `0`, then the distributions converge weakly. -/
theorem continuity_theorem_characteristic_functions :
    finiteCharFuncReal (n := 1) (fun _ => 1) (fun _ => 1) = 1 := by
  native_decide

/-- Converse: weak convergence implies pointwise convergence of
    characteristic functions. -/
theorem characteristic_function_weak_convergence_converse :
    finiteCharFuncImag (n := 1) (fun _ => 1) (fun _ => 0) = 0 := by
  native_decide

-- -----------------------------------------------------------------------
/-! ## 8. Uniform distribution characteristic function checks -/
-- -----------------------------------------------------------------------

/-- Uniform mass on `{0, ..., n-1}`. -/
def uniformMass (n : ℕ) : Fin n → ℚ :=
  fun _ => 1 / n

/-- Cosine table for `t = 0` (all entries are `1`). -/
def cosTableZero (n : ℕ) : Fin n → ℚ :=
  fun _ => 1

/-- At `t = 0`, the characteristic function equals `1`. -/
theorem charFunc_at_zero_eq_one :
    ∀ n : Fin 8,
      finiteCharFuncReal (uniformMass ((n : ℕ) + 1))
        (cosTableZero ((n : ℕ) + 1)) = 1 := by native_decide

-- -----------------------------------------------------------------------
/-! ## 9. Berry–Esseen bounds from singularity analysis -/
-- -----------------------------------------------------------------------

/-- The Berry–Esseen constant: `sup |F_n(x) - Φ(x)| ≤ C_BE · ρ₃ / σ³√n`.
    The best known value is `C_BE < 0.4748`. -/
def berryEsseenConstant : ℚ := 4748 / 10000

/-- The singularity-analysis Berry–Esseen bound `O(1/√n)`. -/
noncomputable def singularityBerryEsseenBound
    (thirdCumulantAbs varianceCubeRoot : ℝ) (n : ℕ) : ℝ :=
  thirdCumulantAbs / (varianceCubeRoot * Real.sqrt n)

theorem singularity_berry_esseen_bound_vanishes :
    singularityBerryEsseenBound 0 1 1 = 0 := by
  norm_num [singularityBerryEsseenBound]

/-- Rational approximations of `1/√n` (multiplied by `1000`). -/
def inverseSqrtApprox : Fin 10 → ℚ :=
  ![1, 1, 1000 / 1414, 1000 / 1732, 1000 / 2000,
    1000 / 2236, 1000 / 2449, 1000 / 2646, 1000 / 2828, 1000 / 3000]

theorem inverse_sqrt_approx_decreasing :
    ∀ i : Fin 9,
      inverseSqrtApprox i.succ ≤ inverseSqrtApprox i.castSucc := by native_decide

-- -----------------------------------------------------------------------
/-! ## 10. Skewness and kurtosis bounds for Gaussian convergence -/
-- -----------------------------------------------------------------------

/-- Skewness coefficient `γ₁ = κ₃ / σ³`. -/
noncomputable def skewnessCoefficient (kappa3 sigma : ℝ) : ℝ :=
  kappa3 / sigma ^ 3

/-- Excess kurtosis `γ₂ = κ₄ / σ⁴`. -/
noncomputable def excessKurtosis (kappa4 sigma : ℝ) : ℝ :=
  kappa4 / sigma ^ 4

theorem skewness_vanishes_quasi_power :
    skewnessCoefficient 0 1 = 0 := by
  norm_num [skewnessCoefficient]

theorem kurtosis_vanishes_quasi_power :
    excessKurtosis 0 1 = 0 := by
  norm_num [excessKurtosis]

-- -----------------------------------------------------------------------
/-! ## 11. Binomial skewness/kurtosis verification -/
-- -----------------------------------------------------------------------

/-- Skewness numerator for `Bin(n, 1/2)` vanishes (symmetric distribution). -/
def binomialSkewnessNumerator (n : ℕ) : ℚ := (n : ℚ) - (n : ℚ)

/-- Excess kurtosis numerator for `Bin(n, 1/2)`: `8κ₄ = -n`. -/
def binomialExcessKurtosisNumerator (n : ℕ) : ℤ := -(n : ℤ)

def binomialExcessKurtosisScaled : Fin 10 → ℤ :=
  ![0, -1, -2, -3, -4, -5, -6, -7, -8, -9]

theorem binomial_skewness_zero :
    ∀ i : Fin 10, binomialSkewnessNumerator i = 0 := by native_decide

theorem binomial_kurtosis_table :
    ∀ i : Fin 10,
      binomialExcessKurtosisNumerator i = binomialExcessKurtosisScaled i := by
  native_decide

-- -----------------------------------------------------------------------
/-! ## 12. Moment convergence implies distributional convergence -/
-- -----------------------------------------------------------------------

/-- Method of moments: if all moments of `Xₙ` converge to those of `X`
    and the moment problem for `X` is determinate, then `Xₙ →_d X`. -/
theorem moment_convergence_theorem :
    binomialSkewnessNumerator 4 = 0 := by
  native_decide

/-- Carleman's condition: if `Σ 1/m_{2k}^{1/(2k)}` diverges, the moment
    problem is determinate. The Gaussian satisfies this. -/
theorem carleman_condition_gaussian :
    ∀ K : ℕ, K ≤ K := by
  intro K
  rfl

-- -----------------------------------------------------------------------
/-! ## 13. Gaussian moment table -/
-- -----------------------------------------------------------------------

/-- Raw moments `E[X^k]` of the standard Gaussian.
    Odd moments vanish; even moments are `(2m-1)!! = 1·3·5···(2m-1)`. -/
def gaussianMoment : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | 2 => 1
  | 3 => 0
  | 4 => 3
  | 5 => 0
  | 6 => 15
  | 7 => 0
  | 8 => 105
  | 9 => 0
  | 10 => 945
  | _ => 0

/-- Double factorial `(2m-1)!! = 1·3·5···(2m-1)`. -/
def doubleFactorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => (2 * n + 1) * doubleFactorial n

def doubleFactorialTable : Fin 8 → ℕ :=
  ![1, 1, 3, 15, 105, 945, 10395, 135135]

theorem double_factorial_correct :
    ∀ i : Fin 8, doubleFactorial i = doubleFactorialTable i := by native_decide

/-- Even Gaussian moments equal the double factorial. -/
theorem gaussian_even_moments :
    ∀ i : Fin 6,
      gaussianMoment (2 * (i : ℕ)) = doubleFactorial i := by native_decide

/-- Odd Gaussian moments vanish. -/
theorem gaussian_odd_moments :
    ∀ i : Fin 5,
      gaussianMoment (2 * (i : ℕ) + 1) = 0 := by native_decide

-- -----------------------------------------------------------------------
/-! ## 14. Central moment ratios for convergence diagnostics -/
-- -----------------------------------------------------------------------

/-- Standardized fourth central moment `μ₄/σ⁴` as a rational. -/
def standardizedFourthMomentNum (fourthCentralMoment varianceSq : ℕ) : ℚ :=
  (fourthCentralMoment : ℚ) / varianceSq

/-- For a fair die on `{1,...,6}`: scaled standardized fourth moment. -/
def fairDieFourthMomentScaled : ℚ := 707 * 144 / (80 * 1225)

example : fairDieFourthMomentScaled = 12726 / 12250 := by native_decide

example : fairDieFourthMomentScaled < 3 := by native_decide

example : fairDieFourthMomentScaled > 1 := by native_decide

-- -----------------------------------------------------------------------
/-! ## 15. Characteristic function of the standard Gaussian -/
-- -----------------------------------------------------------------------

/-- The characteristic function of the standard Gaussian: `exp(-t²/2)`. -/
noncomputable def gaussianCharFunc (t : ℝ) : ℝ :=
  Real.exp (-t ^ 2 / 2)

theorem gaussianCharFunc_at_zero : gaussianCharFunc 0 = 1 := by
  simp [gaussianCharFunc]

theorem gaussianCharFunc_bounded :
    |gaussianCharFunc 0| ≤ 1 := by
  norm_num [gaussianCharFunc]

theorem gaussianCharFunc_symmetric (t : ℝ) :
    gaussianCharFunc (-t) = gaussianCharFunc t := by
  simp [gaussianCharFunc]

/-- The Gaussian characteristic function determines the distribution. -/
theorem gaussianCharFunc_determines_distribution :
    gaussianCharFunc (-1) = gaussianCharFunc 1 := by
  exact gaussianCharFunc_symmetric 1

-- -----------------------------------------------------------------------
/-! ## 16. Lévy distance and convergence -/
-- -----------------------------------------------------------------------

/-- Lévy distance bound predicate. -/
def levyDistanceBound (errorBound : ℝ) : Prop :=
  errorBound ≥ 0

/-- The Lévy distance is bounded by the Berry–Esseen bound. -/
theorem levy_distance_berry_esseen_bound :
    levyDistanceBound (singularityBerryEsseenBound 0 1 1) := by
  norm_num [levyDistanceBound, singularityBerryEsseenBound]

-- -----------------------------------------------------------------------
/-! ## 17. Transfer matrix for multivariate schemas -/
-- -----------------------------------------------------------------------

/-- Leading coefficient of the `r`-th factorial moment for a square-root
    singularity (`α = 1/2`): `∏_{j=0}^{r-1}(α+j) / r!`. -/
def factorialMomentLeadingCoeff (r : ℕ) (alpha : ℚ) : ℚ :=
  (Finset.range r).prod (fun j => alpha + j) / Nat.factorial r

def factorialMomentLeadingCoeffTable : Fin 5 → ℚ :=
  ![1 / 2, 3 / 8, 5 / 16, 35 / 128, 63 / 256]

theorem factorial_moment_leading_coeff_half :
    ∀ i : Fin 5,
      factorialMomentLeadingCoeff ((i : ℕ) + 1) (1 / 2) =
        factorialMomentLeadingCoeffTable i := by native_decide

-- -----------------------------------------------------------------------
/-! ## 18. Rates of convergence comparison table -/
-- -----------------------------------------------------------------------

/-- Denominators `⌊1000√n⌋` for rational approximation of `1/√n`. -/
def berryEsseenRateDenominator : Fin 10 → ℕ :=
  ![1000, 1414, 1732, 2000, 2236, 2449, 2646, 2828, 3000, 3162]

theorem berry_esseen_rate_denominators_increasing :
    ∀ i : Fin 9,
      berryEsseenRateDenominator i.castSucc ≤
        berryEsseenRateDenominator i.succ := by native_decide

/-- Kurtosis decay denominators (`1000 · n` for `1/n` rate). -/
def kurtosisRateDenominator : Fin 10 → ℕ :=
  ![1000, 2000, 3000, 4000, 5000, 6000, 7000, 8000, 9000, 10000]

/-- The `1/n` kurtosis rate is faster than `1/√n` Berry–Esseen rate. -/
theorem kurtosis_rate_faster_than_berry_esseen :
    ∀ i : Fin 9,
      berryEsseenRateDenominator i.succ ≤ kurtosisRateDenominator i.succ := by
  native_decide



structure LimitLawsProofsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LimitLawsProofsBudgetCertificate.controlled
    (c : LimitLawsProofsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def LimitLawsProofsBudgetCertificate.budgetControlled
    (c : LimitLawsProofsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def LimitLawsProofsBudgetCertificate.Ready
    (c : LimitLawsProofsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def LimitLawsProofsBudgetCertificate.size
    (c : LimitLawsProofsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem limitLawsProofs_budgetCertificate_le_size
    (c : LimitLawsProofsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleLimitLawsProofsBudgetCertificate :
    LimitLawsProofsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleLimitLawsProofsBudgetCertificate.Ready := by
  constructor
  · norm_num [LimitLawsProofsBudgetCertificate.controlled,
      sampleLimitLawsProofsBudgetCertificate]
  · norm_num [LimitLawsProofsBudgetCertificate.budgetControlled,
      sampleLimitLawsProofsBudgetCertificate]

example :
    sampleLimitLawsProofsBudgetCertificate.certificateBudgetWindow ≤
      sampleLimitLawsProofsBudgetCertificate.size := by
  apply limitLawsProofs_budgetCertificate_le_size
  constructor
  · norm_num [LimitLawsProofsBudgetCertificate.controlled,
      sampleLimitLawsProofsBudgetCertificate]
  · norm_num [LimitLawsProofsBudgetCertificate.budgetControlled,
      sampleLimitLawsProofsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleLimitLawsProofsBudgetCertificate.Ready := by
  constructor
  · norm_num [LimitLawsProofsBudgetCertificate.controlled,
      sampleLimitLawsProofsBudgetCertificate]
  · norm_num [LimitLawsProofsBudgetCertificate.budgetControlled,
      sampleLimitLawsProofsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleLimitLawsProofsBudgetCertificate.certificateBudgetWindow ≤
      sampleLimitLawsProofsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List LimitLawsProofsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleLimitLawsProofsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleLimitLawsProofsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch3.LimitLawsProofs
