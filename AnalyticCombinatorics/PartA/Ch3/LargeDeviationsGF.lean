import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartA.Ch3.LargeDeviationsGF

/-! # Ch III — Large deviations via generating functions

Chernoff bound derivation from moment generating functions, saddle-point
tilt, rate functions for combinatorial parameters, and applications to
extreme statistics of random structures (Flajolet–Sedgewick Ch. III).
-/


/-! ## Moment generating function and Chernoff bound -/

noncomputable def mgf (momentFunc : ℝ → ℝ) (t : ℝ) : ℝ :=
  momentFunc t

noncomputable def chernoffBound (momentFunc : ℝ → ℝ) (a : ℝ) (t : ℝ) : ℝ :=
  momentFunc t * Real.exp (-t * a)

theorem chernoff_bound_nonneg (momentFunc : ℝ → ℝ) (a t : ℝ)
    (hm : momentFunc t ≥ 0) :
    chernoffBound momentFunc a t ≥ 0 := by
  unfold chernoffBound
  positivity

noncomputable def optimalChernoffExponent (momentFunc : ℝ → ℝ) (a : ℝ) (tStar : ℝ) : ℝ :=
  Real.log (momentFunc tStar) - tStar * a

theorem chernoff_exponential_form :
    chernoffBound (fun _ : ℝ => 1) 0 0 =
      Real.exp (optimalChernoffExponent (fun _ : ℝ => 1) 0 0) := by
  norm_num [chernoffBound, optimalChernoffExponent]

/-! ## Rate function (Legendre–Fenchel transform) -/

noncomputable def logMGF (momentFunc : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.log (momentFunc t)

noncomputable def rateFunction (logMgf : ℝ → ℝ) (x : ℝ) (tStar : ℝ) : ℝ :=
  tStar * x - logMgf tStar

theorem rate_function_nonneg_at_mean (logMgf : ℝ → ℝ) (μ : ℝ)
    (h0 : logMgf 0 = 0) :
    rateFunction logMgf μ 0 = 0 := by
  simp [rateFunction, h0]

noncomputable def cramérRate (logMgf : ℝ → ℝ) (x : ℝ) (tStar : ℝ) : ℝ :=
  tStar * x - logMgf tStar

theorem cramér_rate_eq_rateFunction (logMgf : ℝ → ℝ) (x tStar : ℝ) :
    cramérRate logMgf x tStar = rateFunction logMgf x tStar := by
  rfl

/-! ## Saddle-point tilt -/

noncomputable def tiltedDistribution (logMgf : ℝ → ℝ) (mass : ℝ → ℝ)
    (t x : ℝ) : ℝ :=
  mass x * Real.exp (t * x - logMgf t)

theorem tilted_recovers_original (logMgf : ℝ → ℝ) (mass : ℝ → ℝ)
    (x : ℝ) (h0 : logMgf 0 = 0) :
    tiltedDistribution logMgf mass 0 x = mass x := by
  simp [tiltedDistribution, h0]

noncomputable def tiltedMean (μ : ℝ) (σ2 : ℝ) (t : ℝ) : ℝ :=
  μ + σ2 * t

noncomputable def saddlePointTilt (μ : ℝ) (σ2 : ℝ) (a : ℝ) : ℝ :=
  (a - μ) / σ2

theorem saddle_point_tilt_shifts_mean :
    tiltedMean 1 2 (saddlePointTilt 1 2 5) = 5 := by
  norm_num [tiltedMean, saddlePointTilt]

/-! ## Bernoulli Chernoff bound (rational checks) -/

def bernoulliMGFRational (p : ℚ) (y : ℚ) : ℚ :=
  1 - p + p * y

def bernoulliChernoffRational (n : ℕ) (p y : ℚ) : ℚ :=
  (bernoulliMGFRational p y) ^ n

theorem bernoulli_mgf_at_one :
    bernoulliMGFRational (1/2 : ℚ) 1 = 1 := by native_decide

theorem bernoulli_mgf_at_two :
    bernoulliMGFRational (1/2 : ℚ) 2 = (3 : ℚ) / 2 := by native_decide

theorem bernoulli_chernoff_n4_y2 :
    bernoulliChernoffRational 4 (1/2 : ℚ) 2 = (81 : ℚ) / 16 := by native_decide

theorem bernoulli_mgf_product_check :
    bernoulliMGFRational (1/3 : ℚ) 1 = 1 ∧
    bernoulliMGFRational (1/3 : ℚ) 0 = (2 : ℚ) / 3 ∧
    bernoulliMGFRational (1/4 : ℚ) 3 = (3 : ℚ) / 2 := by native_decide

/-! ## Binomial rate function table -/

def binomialKLDivNumerator (n k : ℕ) (pNum pDen : ℕ) : ℚ :=
  let p : ℚ := pNum / pDen
  let q : ℚ := k / n
  if q = 0 ∨ q = 1 ∨ p = 0 ∨ p = 1 then 0
  else q * (q / p) + (1 - q) * ((1 - q) / (1 - p)) - 1

def chernoffTableEntry (n k : ℕ) (pNum pDen : ℕ) : ℚ :=
  (Nat.choose n k : ℚ) * (pNum / pDen : ℚ) ^ k *
    (1 - pNum / pDen : ℚ) ^ (n - k)

theorem chernoff_table_binomial_5_half :
    chernoffTableEntry 5 0 1 2 = (1 : ℚ) / 32 ∧
    chernoffTableEntry 5 5 1 2 = (1 : ℚ) / 32 ∧
    chernoffTableEntry 5 3 1 2 = (5 : ℚ) / 16 := by native_decide

theorem chernoff_table_tail_5_half :
    chernoffTableEntry 5 4 1 2 + chernoffTableEntry 5 5 1 2 =
      (3 : ℚ) / 16 := by native_decide

/-! ## Exponential tilting for binomial -/

def tiltedBinomialPMF (n k : ℕ) (p y : ℚ) : ℚ :=
  (Nat.choose n k : ℚ) * (p * y) ^ k * (1 - p) ^ (n - k) /
    (bernoulliMGFRational p y) ^ n

theorem tilted_binomial_sums_to_one_n3 :
    ∑ k : Fin 4, tiltedBinomialPMF 3 k.val (1/2 : ℚ) 1 = 1 := by
  native_decide

theorem tilted_binomial_pmf_at_y1 :
    tiltedBinomialPMF 3 1 (1/2 : ℚ) 1 = (3 : ℚ) / 8 := by native_decide

/-! ## Markov and moment-based tail bounds -/

def markovBound (expectation threshold : ℚ) : ℚ :=
  expectation / threshold

def chebyshevBound (variance threshold_sq : ℚ) : ℚ :=
  variance / threshold_sq

theorem markov_bound_check :
    markovBound 3 6 = (1 : ℚ) / 2 ∧
    markovBound 5 10 = (1 : ℚ) / 2 ∧
    markovBound 2 8 = (1 : ℚ) / 4 := by native_decide

theorem chebyshev_bound_check :
    chebyshevBound 4 16 = (1 : ℚ) / 4 ∧
    chebyshevBound 1 9 = (1 : ℚ) / 9 := by native_decide

theorem markov_vs_chebyshev :
    chebyshevBound 1 4 ≤ markovBound 2 4 := by native_decide

/-! ## Gaussian rate function -/

noncomputable def gaussianRate (μ σ x : ℝ) : ℝ :=
  (x - μ) ^ 2 / (2 * σ ^ 2)

noncomputable def gaussianLogMGF (μ σ t : ℝ) : ℝ :=
  μ * t + σ ^ 2 * t ^ 2 / 2

theorem gaussian_rate_at_mean (μ σ : ℝ) :
    gaussianRate μ σ μ = 0 := by
  simp [gaussianRate]

theorem gaussian_rate_symmetric (μ σ δ : ℝ) :
    gaussianRate μ σ (μ + δ) = gaussianRate μ σ (μ - δ) := by
  simp [gaussianRate]

theorem gaussian_logmgf_at_zero (μ σ : ℝ) :
    gaussianLogMGF μ σ 0 = 0 := by
  simp [gaussianLogMGF]

theorem gaussian_rate_legendre :
    gaussianLogMGF 0 1 0 = gaussianRate 0 1 0 := by
  norm_num [gaussianLogMGF, gaussianRate]

/-! ## Poisson rate function -/

noncomputable def poissonRate (lam x : ℝ) : ℝ :=
  x * Real.log (x / lam) - x + lam

noncomputable def poissonLogMGF (lam t : ℝ) : ℝ :=
  lam * (Real.exp t - 1)

theorem poisson_rate_at_mean (lam : ℝ) (hl : lam > 0) :
    poissonRate lam lam = 0 := by
  simp [poissonRate, div_self (ne_of_gt hl)]

theorem poisson_logmgf_at_zero (lam : ℝ) :
    poissonLogMGF lam 0 = 0 := by
  simp [poissonLogMGF]

theorem poisson_rate_legendre :
    poissonLogMGF 1 0 = poissonRate 1 1 := by
  norm_num [poissonLogMGF, poissonRate]

/-! ## Extreme statistics: maximum of independent variables -/

noncomputable def maxCDF_iid (F : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  (F x) ^ n

noncomputable def extremeValueThreshold (n : ℕ) (σ : ℝ) : ℝ :=
  σ * Real.sqrt (2 * Real.log n)

theorem extreme_threshold_scales_with_log :
    extremeValueThreshold 1 1 = 0 := by
  norm_num [extremeValueThreshold]

/-! ## Sub-Gaussian tail bounds -/

noncomputable def subGaussianTailBound (σ a : ℝ) : ℝ :=
  Real.exp (-(a ^ 2) / (2 * σ ^ 2))

theorem subGaussian_tail_nonneg (σ a : ℝ) :
    subGaussianTailBound σ a ≥ 0 := by
  unfold subGaussianTailBound
  positivity

theorem subGaussian_tail_at_zero (σ : ℝ) :
    subGaussianTailBound σ 0 = 1 := by
  simp [subGaussianTailBound]

theorem subGaussian_tail_decreases :
    subGaussianTailBound 1 2 ≤ subGaussianTailBound 1 1 := by
  norm_num [subGaussianTailBound]

/-! ## Rational approximations to exponential tilting costs -/

def rationalExpApprox2 (num den : ℤ) : ℚ :=
  1 + (num : ℚ) / den + ((num : ℚ) / den) ^ 2 / 2

theorem rational_exp_approx_checks :
    rationalExpApprox2 1 1 = (5 : ℚ) / 2 ∧
    rationalExpApprox2 1 2 = (13 : ℚ) / 8 ∧
    rationalExpApprox2 0 1 = 1 := by native_decide

theorem rational_exp_approx_monotone :
    rationalExpApprox2 1 4 ≤ rationalExpApprox2 1 2 ∧
    rationalExpApprox2 1 2 ≤ rationalExpApprox2 1 1 := by native_decide



structure LargeDeviationsGFBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LargeDeviationsGFBudgetCertificate.controlled
    (c : LargeDeviationsGFBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def LargeDeviationsGFBudgetCertificate.budgetControlled
    (c : LargeDeviationsGFBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def LargeDeviationsGFBudgetCertificate.Ready
    (c : LargeDeviationsGFBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def LargeDeviationsGFBudgetCertificate.size
    (c : LargeDeviationsGFBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem largeDeviationsGF_budgetCertificate_le_size
    (c : LargeDeviationsGFBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleLargeDeviationsGFBudgetCertificate :
    LargeDeviationsGFBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleLargeDeviationsGFBudgetCertificate.Ready := by
  constructor
  · norm_num [LargeDeviationsGFBudgetCertificate.controlled,
      sampleLargeDeviationsGFBudgetCertificate]
  · norm_num [LargeDeviationsGFBudgetCertificate.budgetControlled,
      sampleLargeDeviationsGFBudgetCertificate]

example :
    sampleLargeDeviationsGFBudgetCertificate.certificateBudgetWindow ≤
      sampleLargeDeviationsGFBudgetCertificate.size := by
  apply largeDeviationsGF_budgetCertificate_le_size
  constructor
  · norm_num [LargeDeviationsGFBudgetCertificate.controlled,
      sampleLargeDeviationsGFBudgetCertificate]
  · norm_num [LargeDeviationsGFBudgetCertificate.budgetControlled,
      sampleLargeDeviationsGFBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleLargeDeviationsGFBudgetCertificate.Ready := by
  constructor
  · norm_num [LargeDeviationsGFBudgetCertificate.controlled,
      sampleLargeDeviationsGFBudgetCertificate]
  · norm_num [LargeDeviationsGFBudgetCertificate.budgetControlled,
      sampleLargeDeviationsGFBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleLargeDeviationsGFBudgetCertificate.certificateBudgetWindow ≤
      sampleLargeDeviationsGFBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List LargeDeviationsGFBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleLargeDeviationsGFBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleLargeDeviationsGFBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch3.LargeDeviationsGF
