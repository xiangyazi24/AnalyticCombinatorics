import AnalyticCombinatorics.Ch8.SaddlePoint.Exp
import AnalyticCombinatorics.Ch2.EGF.Applications
import Mathlib.Analysis.Analytic.Composition
import Mathlib.RingTheory.PowerSeries.Substitution

open Complex
open scoped NNReal ENNReal

noncomputable section

abbrev bellCoeffR (n : ℕ) : ℝ :=
  (AnalyticCombinatorics.Ch1.CombClass.posInt.set.counts n : ℝ) / n.factorial

lemma bellCoeffR_nonneg (n : ℕ) : 0 ≤ bellCoeffR n := by
  positivity

def bellCarrier : PowerSeries ℂ :=
  PowerSeries.mapℂ AnalyticCombinatorics.Ch1.CombClass.posInt.set.egf

@[simp] theorem bellCarrier_coeff (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n bellCarrier = (bellCoeffR n : ℂ) := by
  simp [bellCarrier, bellCoeffR, AnalyticCombinatorics.Ch1.CombClass.coeff_egf]

def bellCarrier_nonneg : NonnegRealCoeff bellCarrier where
  coeffR := bellCoeffR
  coeff_nonneg := bellCoeffR_nonneg
  coeff_eq := bellCarrier_coeff

theorem bellCarrier_norm_coeff (n : ℕ) :
    ‖PowerSeries.coeff (R := ℂ) n bellCarrier‖ = bellCoeffR n := by
  rw [bellCarrier_coeff]
  simp

theorem bellCarrier_eq_complex_subst :
    bellCarrier = (PowerSeries.exp ℂ).subst (PowerSeries.exp ℂ - 1) := by
  rw [bellCarrier, AnalyticCombinatorics.Ch1.CombClass.egf_bell]
  have hsubst : PowerSeries.HasSubst (PowerSeries.exp ℚ - 1 : PowerSeries ℚ) := by
    apply PowerSeries.HasSubst.of_constantCoeff_zero'
    simp
  change (PowerSeries.map (algebraMap ℚ ℂ)
      ((PowerSeries.exp ℚ).subst (PowerSeries.exp ℚ - 1))) = _
  simpa using
    (PowerSeries.map_subst (a := (PowerSeries.exp ℚ - 1 : PowerSeries ℚ))
      (h := algebraMap ℚ ℂ) hsubst (PowerSeries.exp ℚ))

noncomputable abbrev analyticBellFun (z : ℂ) : ℂ :=
  Complex.exp (Complex.exp z - 1)

lemma exp_re_le_exp_norm (z : ℂ) :
    (Complex.exp z).re ≤ Real.exp ‖z‖ := by
  calc
    (Complex.exp z).re = Real.exp z.re * Real.cos z.im := by
      rw [Complex.exp_re]
    _ ≤ Real.exp z.re * 1 := by
      exact mul_le_mul_of_nonneg_left (Real.cos_le_one z.im) (Real.exp_pos z.re).le
    _ = Real.exp z.re := by ring
    _ ≤ Real.exp ‖z‖ := by
      exact Real.exp_le_exp.mpr (Complex.re_le_norm z)

lemma analyticBell_norm_le_of_norm_le {R : ℝ} {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖analyticBellFun z‖ ≤ Real.exp (Real.exp R - 1) := by
  have hzre : (Complex.exp z).re ≤ Real.exp R :=
    (exp_re_le_exp_norm z).trans (Real.exp_le_exp.mpr hz)
  rw [analyticBellFun, Complex.norm_exp]
  exact Real.exp_le_exp.mpr (sub_le_sub_right hzre 1)

lemma analyticBell_differentiableOn (R : ℝ) :
    DifferentiableOn ℂ analyticBellFun (Metric.closedBall 0 R) := by
  unfold analyticBellFun
  fun_prop

noncomputable abbrev expSeriesC : FormalMultilinearSeries ℂ ℂ ℂ :=
  NormedSpace.expSeries ℂ ℂ

noncomputable abbrev analyticBellSeries : FormalMultilinearSeries ℂ ℂ ℂ :=
  expSeriesC.comp (expSeriesC - constFormalMultilinearSeries ℂ ℂ (1 : ℂ))

lemma exp_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt Complex.exp expSeriesC (0 : ℂ) := by
  have hsum : HasFPowerSeriesAt expSeriesC.sum expSeriesC (0 : ℂ) := by
    exact (expSeriesC.hasFPowerSeriesOnBall
      (by
        rw [expSeriesC, NormedSpace.expSeries_radius_eq_top]
        exact WithTop.top_pos)).hasFPowerSeriesAt
  have hfun : expSeriesC.sum = Complex.exp := by
    funext z
    calc
      expSeriesC.sum z = NormedSpace.exp z := by
        exact congrFun (NormedSpace.exp_eq_expSeries_sum ℂ).symm z
      _ = Complex.exp z := by
        exact (congrFun Complex.exp_eq_exp_ℂ z).symm
  rwa [hfun] at hsum

lemma exp_sub_one_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt (fun z : ℂ => Complex.exp z - 1)
      (expSeriesC - constFormalMultilinearSeries ℂ ℂ (1 : ℂ)) (0 : ℂ) := by
  simpa using
    (exp_hasFPowerSeriesAt_zero.sub
      (hasFPowerSeriesAt_const (𝕜 := ℂ) (e := (0 : ℂ)) (c := (1 : ℂ))))

lemma analyticBell_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt analyticBellFun analyticBellSeries (0 : ℂ) := by
  have houter : HasFPowerSeriesAt Complex.exp expSeriesC
      ((fun z : ℂ => Complex.exp z - 1) 0) := by
    simpa using exp_hasFPowerSeriesAt_zero
  have h := HasFPowerSeriesAt.comp (g := Complex.exp)
    (f := fun z : ℂ => Complex.exp z - 1)
    houter exp_sub_one_hasFPowerSeriesAt_zero
  simpa [Function.comp_def, analyticBellFun, analyticBellSeries] using h

/-- Bell saddle bound, assuming the analytic Bell function has the formal Bell
carrier as its Taylor series at zero.  This is the exact composition bridge still
needed for the unconditional theorem. -/
theorem bell_egf_coeff_le_of_hasFPowerSeriesAt
    {n : ℕ} {r : ℝ} (hr : 0 < r)
    (hp : HasFPowerSeriesAt analyticBellFun (PowerSeries.toFMLS bellCarrier) (0 : ℂ)) :
    (AnalyticCombinatorics.Ch1.CombClass.posInt.set.counts n : ℝ) / n.factorial ≤
      Real.exp (Real.exp r - 1) / r ^ n := by
  have hM : ∀ z ∈ Metric.sphere (0 : ℂ) r,
      ‖analyticBellFun z‖ ≤ Real.exp (Real.exp r - 1) := by
    intro z hz
    have hz_norm : ‖z‖ = r := by
      simpa [dist_eq_norm] using (Metric.mem_sphere.1 hz)
    exact analyticBell_norm_le_of_norm_le (R := r) (z := z) hz_norm.le
  have hbound := norm_coeff_le_of_circleIntegral (f := analyticBellFun)
    (p := PowerSeries.toFMLS bellCarrier) (R := r)
    (M := Real.exp (Real.exp r - 1))
    hr hp (analyticBell_differentiableOn r) hM n
  have hbound_coeff : ‖PowerSeries.coeff (R := ℂ) n bellCarrier‖ ≤
      Real.exp (Real.exp r - 1) * r⁻¹ ^ n := by
    simpa using hbound
  calc
    (AnalyticCombinatorics.Ch1.CombClass.posInt.set.counts n : ℝ) / n.factorial
        = ‖PowerSeries.coeff (R := ℂ) n bellCarrier‖ := by
            rw [bellCarrier_norm_coeff]
    _ ≤ Real.exp (Real.exp r - 1) * r⁻¹ ^ n := hbound_coeff
    _ = Real.exp (Real.exp r - 1) / r ^ n := by
      rw [inv_pow]
      ring

theorem bell_egf_coeff_le_of_composition_bridge
    {n : ℕ} {r : ℝ} (hr : 0 < r)
    (hbridge : PowerSeries.toFMLS bellCarrier = analyticBellSeries) :
    (AnalyticCombinatorics.Ch1.CombClass.posInt.set.counts n : ℝ) / n.factorial ≤
      Real.exp (Real.exp r - 1) / r ^ n := by
  have hp : HasFPowerSeriesAt analyticBellFun
      (PowerSeries.toFMLS bellCarrier) (0 : ℂ) := by
    simpa [hbridge] using analyticBell_hasFPowerSeriesAt_zero
  exact bell_egf_coeff_le_of_hasFPowerSeriesAt hr hp

theorem bell_egf_coeff_le_of_analyticSum
    {n : ℕ} {r : ℝ} (hr : 0 < r)
    (hball : 0 < (PowerSeries.toFMLS bellCarrier).radius)
    (hrmem : (r : ℂ) ∈ Metric.eball 0 (PowerSeries.toFMLS bellCarrier).radius)
    (hd : DifferentiableOn ℂ (PowerSeries.analyticSum bellCarrier) (Metric.closedBall 0 r))
    (hval : (PowerSeries.analyticSum bellCarrier (r : ℂ)).re =
      Real.exp (Real.exp r - 1)) :
    (AnalyticCombinatorics.Ch1.CombClass.posInt.set.counts n : ℝ) / n.factorial ≤
      Real.exp (Real.exp r - 1) / r ^ n := by
  have hbound :=
    PowerSeries.norm_coeff_le_analyticSum_of_nonneg bellCarrier_nonneg hr hball hrmem hd n
  calc
    (AnalyticCombinatorics.Ch1.CombClass.posInt.set.counts n : ℝ) / n.factorial
        = ‖PowerSeries.coeff (R := ℂ) n bellCarrier‖ := by
            rw [bellCarrier_norm_coeff]
    _ ≤ (PowerSeries.analyticSum bellCarrier (r : ℂ)).re * r⁻¹ ^ n := hbound
    _ = Real.exp (Real.exp r - 1) * r⁻¹ ^ n := by rw [hval]
    _ = Real.exp (Real.exp r - 1) / r ^ n := by
      rw [inv_pow]
      ring
