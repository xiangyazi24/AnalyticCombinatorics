import AnalyticCombinatorics.Ch4.Analytic.CauchyCoeff

open Complex
open scoped NNReal ENNReal

noncomputable section

structure NonnegRealCoeff (F : PowerSeries ℂ) where
  coeffR : ℕ → ℝ
  coeff_nonneg : ∀ n, 0 ≤ coeffR n
  coeff_eq : ∀ n, PowerSeries.coeff (R := ℂ) n F = (coeffR n : ℂ)

namespace PowerSeries

lemma norm_analyticSum_le_re_analyticSum_of_nonneg
    {F : PowerSeries ℂ} (hF : NonnegRealCoeff F)
    {R : ℝ} {z : ℂ} (hz : ‖z‖ ≤ R)
    (hRmem : (R : ℂ) ∈ Metric.eball 0 F.toFMLS.radius) :
    ‖F.analyticSum z‖ ≤ (F.analyticSum (R : ℂ)).re := by
  have hRsum := PowerSeries.hasSum_analyticSum_of_mem F hRmem
  have hreal_hasSum :
      HasSum (fun n : ℕ => hF.coeffR n * R ^ n)
        (F.analyticSum (R : ℂ)).re := by
    have hre := Complex.reCLM.hasSum hRsum
    simpa [hF.coeff_eq, Complex.ofReal_mul, ← Complex.ofReal_pow] using hre
  rw [PowerSeries.analyticSum_eq_tsum]
  refine tsum_of_norm_bounded hreal_hasSum ?_
  intro n
  have hpow : ‖z‖ ^ n ≤ R ^ n :=
    pow_le_pow_left₀ (norm_nonneg z) hz n
  calc
    ‖PowerSeries.coeff (R := ℂ) n F * z ^ n‖ = hF.coeffR n * ‖z‖ ^ n := by
      simp [hF.coeff_eq n, norm_pow, Real.norm_of_nonneg (hF.coeff_nonneg n)]
    _ ≤ hF.coeffR n * R ^ n := by
      exact mul_le_mul_of_nonneg_left hpow (hF.coeff_nonneg n)

theorem norm_coeff_le_analyticSum_of_nonneg
    {F : PowerSeries ℂ} (hF : NonnegRealCoeff F)
    {R : ℝ} (hR : 0 < R)
    (hball : 0 < F.toFMLS.radius)
    (hRmem : (R : ℂ) ∈ Metric.eball 0 F.toFMLS.radius)
    (hd : DifferentiableOn ℂ F.analyticSum (Metric.closedBall 0 R))
    (n : ℕ) :
    ‖PowerSeries.coeff (R := ℂ) n F‖ ≤
      (F.analyticSum (R : ℂ)).re * R⁻¹ ^ n := by
  have hp : HasFPowerSeriesAt F.analyticSum F.toFMLS 0 :=
    (PowerSeries.hasFPowerSeriesOnBall_analyticSum F hball).hasFPowerSeriesAt
  have hM :
      ∀ z ∈ Metric.sphere (0 : ℂ) R,
        ‖F.analyticSum z‖ ≤ (F.analyticSum (R : ℂ)).re := by
    intro z hz
    have hz_norm : ‖z‖ = R := by
      simpa [dist_eq_norm] using (Metric.mem_sphere.1 hz)
    exact PowerSeries.norm_analyticSum_le_re_analyticSum_of_nonneg hF hz_norm.le hRmem
  have hbound :=
    norm_coeff_le_of_circleIntegral (f := F.analyticSum) (p := F.toFMLS)
      hR hp hd hM n
  simpa [PowerSeries.coeff_toFMLS] using hbound

end PowerSeries

theorem saddle_point_bound_mk
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) {R : ℝ} (hR : 0 < R)
    (hball :
      0 < (PowerSeries.toFMLS
        (PowerSeries.mk fun n => (a n : ℂ))).radius)
    (hRmem :
      (R : ℂ) ∈ Metric.eball 0
        (PowerSeries.toFMLS
          (PowerSeries.mk fun n => (a n : ℂ))).radius)
    (hd :
      DifferentiableOn ℂ
        (PowerSeries.analyticSum
          (PowerSeries.mk fun n => (a n : ℂ)))
        (Metric.closedBall 0 R))
    (n : ℕ) :
    ‖PowerSeries.coeff (R := ℂ) n
        (PowerSeries.mk fun n => (a n : ℂ))‖ ≤
      (PowerSeries.analyticSum
        (PowerSeries.mk fun n => (a n : ℂ)) (R : ℂ)).re * R⁻¹ ^ n := by
  have hF : NonnegRealCoeff (PowerSeries.mk fun n => (a n : ℂ)) := {
    coeffR := a
    coeff_nonneg := ha
    coeff_eq := by
      intro n
      simp
  }
  exact PowerSeries.norm_coeff_le_analyticSum_of_nonneg hF hR hball hRmem hd n
