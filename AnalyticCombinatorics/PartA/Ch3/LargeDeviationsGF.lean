import Mathlib.Tactic
set_option linter.style.nativeDecide false

/-! # Ch III — Large deviations via generating functions

Chernoff bound derivation from moment generating functions, saddle-point
tilt, rate functions for combinatorial parameters, and applications to
extreme statistics of random structures (Flajolet–Sedgewick Ch. III).
-/

namespace LargeDeviationsGF

/-! ## Moment generating function and Chernoff bound -/

noncomputable def mgf (momentFunc : ℝ → ℝ) (t : ℝ) : ℝ :=
  momentFunc t

noncomputable def chernoffBound (momentFunc : ℝ → ℝ) (a : ℝ) (t : ℝ) : ℝ :=
  momentFunc t * Real.exp (-t * a)

theorem chernoff_bound_nonneg (momentFunc : ℝ → ℝ) (a t : ℝ)
    (hm : momentFunc t ≥ 0) :
    chernoffBound momentFunc a t ≥ 0 := by
  sorry

noncomputable def optimalChernoffExponent (momentFunc : ℝ → ℝ) (a : ℝ) (tStar : ℝ) : ℝ :=
  Real.log (momentFunc tStar) - tStar * a

theorem chernoff_exponential_form (momentFunc : ℝ → ℝ) (a tStar : ℝ)
    (hm : momentFunc tStar > 0) :
    chernoffBound momentFunc a tStar =
      Real.exp (optimalChernoffExponent momentFunc a tStar) := by
  sorry

/-! ## Rate function (Legendre–Fenchel transform) -/

noncomputable def logMGF (momentFunc : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.log (momentFunc t)

noncomputable def rateFunction (logMgf : ℝ → ℝ) (x : ℝ) (tStar : ℝ) : ℝ :=
  tStar * x - logMgf tStar

theorem rate_function_nonneg_at_mean (logMgf : ℝ → ℝ) (μ : ℝ)
    (h0 : logMgf 0 = 0) :
    rateFunction logMgf μ 0 = 0 := by
  sorry

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
  sorry

noncomputable def tiltedMean (μ : ℝ) (σ2 : ℝ) (t : ℝ) : ℝ :=
  μ + σ2 * t

noncomputable def saddlePointTilt (μ : ℝ) (σ2 : ℝ) (a : ℝ) : ℝ :=
  (a - μ) / σ2

theorem saddle_point_tilt_shifts_mean (μ σ2 a : ℝ) (hσ : σ2 ≠ 0) :
    tiltedMean μ σ2 (saddlePointTilt μ σ2 a) = a := by
  sorry

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
  sorry

theorem gaussian_rate_symmetric (μ σ δ : ℝ) :
    gaussianRate μ σ (μ + δ) = gaussianRate μ σ (μ - δ) := by
  sorry

theorem gaussian_logmgf_at_zero (μ σ : ℝ) :
    gaussianLogMGF μ σ 0 = 0 := by
  sorry

theorem gaussian_rate_legendre (μ σ t x : ℝ) (hσ : σ ≠ 0)
    (ht : t = (x - μ) / σ ^ 2) :
    t * x - gaussianLogMGF μ σ t = gaussianRate μ σ x := by
  sorry

/-! ## Poisson rate function -/

noncomputable def poissonRate (lam x : ℝ) : ℝ :=
  x * Real.log (x / lam) - x + lam

noncomputable def poissonLogMGF (lam t : ℝ) : ℝ :=
  lam * (Real.exp t - 1)

theorem poisson_rate_at_mean (lam : ℝ) (hl : lam > 0) :
    poissonRate lam lam = 0 := by
  sorry

theorem poisson_logmgf_at_zero (lam : ℝ) :
    poissonLogMGF lam 0 = 0 := by
  sorry

theorem poisson_rate_legendre (lam t : ℝ) (hl : lam > 0) :
    let x := lam * Real.exp t
    t * x - poissonLogMGF lam t = poissonRate lam x := by
  sorry

/-! ## Extreme statistics: maximum of independent variables -/

noncomputable def maxCDF_iid (F : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  (F x) ^ n

noncomputable def extremeValueThreshold (n : ℕ) (σ : ℝ) : ℝ :=
  σ * Real.sqrt (2 * Real.log n)

theorem extreme_threshold_scales_with_log (n : ℕ) (σ : ℝ)
    (hn : (n : ℝ) > 1) (hσ : σ > 0) :
    extremeValueThreshold n σ > 0 := by
  sorry

/-! ## Sub-Gaussian tail bounds -/

noncomputable def subGaussianTailBound (σ a : ℝ) : ℝ :=
  Real.exp (-(a ^ 2) / (2 * σ ^ 2))

theorem subGaussian_tail_nonneg (σ a : ℝ) :
    subGaussianTailBound σ a ≥ 0 := by
  sorry

theorem subGaussian_tail_at_zero (σ : ℝ) :
    subGaussianTailBound σ 0 = 1 := by
  sorry

theorem subGaussian_tail_decreases (σ a b : ℝ) (hσ : σ > 0)
    (hab : 0 ≤ a) (hb : a < b) :
    subGaussianTailBound σ b ≤ subGaussianTailBound σ a := by
  sorry

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

end LargeDeviationsGF
