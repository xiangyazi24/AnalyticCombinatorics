import Mathlib
import AnalyticCombinatorics.Ch8.SaddlePoint.HAdmissible
import AnalyticCombinatorics.Ch8.SaddlePoint.ExpHAdmissible
import AnalyticCombinatorics.Ch8.SaddlePoint.BellHAdmissible
import AnalyticCombinatorics.Ch8.SaddlePoint.ExpStirling
import AnalyticCombinatorics.Ch2.EGF.Applications
import AnalyticCombinatorics.Ch4.Analytic.SubstComp

/-!
# Involution H-admissible saddle data

This file records the Hayman data for the involution EGF
`exp (z + z^2 / 2)`.  The saddle data are
`a(r)=r+r^2`, `b(r)=r+2r^2`, and `δ(r)=r^(-3/4)`.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval PowerSeries

noncomputable section

namespace InvolutionHAdmissible

abbrev involCoeffR (n : ℕ) : ℝ :=
  (AnalyticCombinatorics.Ch1.CombClass.parts12.set.counts n : ℝ) / n.factorial

lemma involCoeffR_nonneg (n : ℕ) : 0 ≤ involCoeffR n := by
  positivity

/-- The genuine complex EGF carrier coming from the Ch2 involution class. -/
def involCarrier : PowerSeries ℂ :=
  PowerSeries.mapℂ AnalyticCombinatorics.Ch1.CombClass.parts12.set.egf

@[simp] theorem involCarrier_coeff (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n involCarrier = (involCoeffR n : ℂ) := by
  simp [involCarrier, involCoeffR, AnalyticCombinatorics.Ch1.CombClass.coeff_egf]

/-- The formal series used by the H-admissible interface. -/
noncomputable abbrev involSeries : FormalMultilinearSeries ℂ ℂ ℂ :=
  PowerSeries.toFMLS involCarrier

/-- The analytic function `exp (z + z^2/2)`. -/
abbrev involFun (z : ℂ) : ℂ :=
  Complex.exp (z + z ^ 2 / 2)

/-- The quadratic inner PowerSeries `z + z^2/2`. -/
def involInnerPS : PowerSeries ℂ :=
  (PowerSeries.X : PowerSeries ℂ) + (2⁻¹ : ℂ) • (PowerSeries.X : PowerSeries ℂ) ^ 2

lemma involInnerPS_constantCoeff : PowerSeries.constantCoeff involInnerPS = 0 := by
  simp [involInnerPS]

theorem involCarrier_eq_complex_subst :
    involCarrier = (PowerSeries.exp ℂ).subst involInnerPS := by
  rw [involCarrier, AnalyticCombinatorics.Ch1.CombClass.egf_involutions]
  have hsubst : PowerSeries.HasSubst
      ((PowerSeries.X : PowerSeries ℚ) + (2⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 2) := by
    apply PowerSeries.HasSubst.of_constantCoeff_zero'
    simp
  have hmap_inner :
      (((PowerSeries.X : PowerSeries ℚ) +
          (2⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 2).map (algebraMap ℚ ℂ)) =
        involInnerPS := by
    ext n
    by_cases hn : n = 2
    · subst n
      norm_num [involInnerPS, PowerSeries.coeff_map, PowerSeries.coeff_X_pow]
    · simp [involInnerPS, PowerSeries.coeff_map, PowerSeries.coeff_X_pow, hn]
  have hmap_exp :
      (PowerSeries.exp ℚ).map (algebraMap ℚ ℂ) = PowerSeries.exp ℂ := by
    ext n
    simp
  change (((PowerSeries.exp ℚ).subst
        ((PowerSeries.X : PowerSeries ℚ) + (2⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 2)).map
      (algebraMap ℚ ℂ)) = _
  rw [PowerSeries.map_subst
    (a := ((PowerSeries.X : PowerSeries ℚ) +
      (2⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 2))
    (h := algebraMap ℚ ℂ) hsubst (PowerSeries.exp ℚ)]
  rw [hmap_exp]
  change (PowerSeries.exp ℂ).subst
      ((((PowerSeries.X : PowerSeries ℚ) +
        (2⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 2).map (algebraMap ℚ ℂ))) =
    (PowerSeries.exp ℂ).subst involInnerPS
  rw [hmap_inner]

lemma hasFPowerSeriesAt_id_toFMLS_X :
    HasFPowerSeriesAt (fun z : ℂ => z)
      (PowerSeries.toFMLS (PowerSeries.X : PowerSeries ℂ)) (0 : ℂ) := by
  rw [hasFPowerSeriesAt_iff]
  filter_upwards with z
  let term : ℕ → ℂ :=
    fun n => z ^ n • (PowerSeries.toFMLS (PowerSeries.X : PowerSeries ℂ)).coeff n
  have hsingle : HasSum term (term 1) := by
    apply hasSum_single
    intro n hn
    simp [term, PowerSeries.coeff_X, hn]
  convert hsingle using 1
  simp [term, PowerSeries.toFMLS]

lemma hasFPowerSeriesAt_mul_toFMLS {f g : ℂ → ℂ} {F G : PowerSeries ℂ}
    (hf : HasFPowerSeriesAt f (PowerSeries.toFMLS F) (0 : ℂ))
    (hg : HasFPowerSeriesAt g (PowerSeries.toFMLS G) (0 : ℂ)) :
    HasFPowerSeriesAt (fun z : ℂ => f z * g z)
      (PowerSeries.toFMLS (F * G)) (0 : ℂ) := by
  rcases hf with ⟨rf, hrf⟩
  rcases hg with ⟨rg, hrg⟩
  rw [hasFPowerSeriesAt_iff]
  refine eventually_of_mem
    (Metric.eball_mem_nhds (0 : ℂ) (lt_min hrf.r_pos hrg.r_pos)) ?_
  intro z hz
  have hzf : z ∈ Metric.eball (0 : ℂ) rf := by
    exact Metric.mem_eball.mpr
      (lt_of_lt_of_le (Metric.mem_eball.mp hz) (min_le_left _ _))
  have hzg : z ∈ Metric.eball (0 : ℂ) rg := by
    exact Metric.mem_eball.mpr
      (lt_of_lt_of_le (Metric.mem_eball.mp hz) (min_le_right _ _))
  let a : ℕ → ℂ := fun n => z ^ n * PowerSeries.coeff (R := ℂ) n F
  let b : ℕ → ℂ := fun n => z ^ n * PowerSeries.coeff (R := ℂ) n G
  have hsumf : HasSum a (f z) := by
    have h := hrf.hasSum hzf
    simpa [a, PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars, smul_eq_mul,
      mul_comm, mul_left_comm, mul_assoc] using h
  have hsumg : HasSum b (g z) := by
    have h := hrg.hasSum hzg
    simpa [b, PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars, smul_eq_mul,
      mul_comm, mul_left_comm, mul_assoc] using h
  have hzfrad : z ∈ Metric.eball (0 : ℂ) (PowerSeries.toFMLS F).radius :=
    Metric.eball_subset_eball hrf.r_le hzf
  have hzgrad : z ∈ Metric.eball (0 : ℂ) (PowerSeries.toFMLS G).radius :=
    Metric.eball_subset_eball hrg.r_le hzg
  have hnormf : Summable fun n : ℕ => ‖a n‖ := by
    simpa [a, PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars, smul_eq_mul,
      mul_comm, mul_left_comm, mul_assoc] using
      (PowerSeries.toFMLS F).summable_norm_apply hzfrad
  have hnormg : Summable fun n : ℕ => ‖b n‖ := by
    simpa [b, PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars, smul_eq_mul,
      mul_comm, mul_left_comm, mul_assoc] using
      (PowerSeries.toFMLS G).summable_norm_apply hzgrad
  let cseq : ℕ → ℂ := fun n => z ^ n * PowerSeries.coeff (R := ℂ) n (F * G)
  let d : ℕ → ℂ := fun n => ∑ kl ∈ Finset.antidiagonal n, a kl.1 * b kl.2
  have hcd : ∀ n, cseq n = d n := by
    intro n
    change z ^ n * PowerSeries.coeff (R := ℂ) n (F * G) =
      ∑ kl ∈ Finset.antidiagonal n, a kl.1 * b kl.2
    rw [PowerSeries.coeff_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro kl hkl
    have hsum : kl.1 + kl.2 = n := Finset.mem_antidiagonal.mp hkl
    simp [a, b]
    rw [← hsum, pow_add]
    ring
  have hnormd : Summable fun n : ℕ => ‖d n‖ := by
    simpa [d] using summable_norm_sum_mul_antidiagonal_of_summable_norm hnormf hnormg
  have hnormc : Summable fun n : ℕ => ‖cseq n‖ := by
    exact hnormd.congr (fun n => by rw [hcd n])
  have hsumc : Summable cseq := hnormc.of_norm
  have htsum : (∑' n : ℕ, cseq n) = f z * g z := by
    have hprod := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hnormf hnormg
    rw [hsumf.tsum_eq, hsumg.tsum_eq] at hprod
    rw [tsum_congr hcd, ← hprod]
  have hmain : HasSum cseq (f z * g z) := hsumc.hasSum_iff.mpr htsum
  simpa [cseq, PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars, smul_eq_mul,
    mul_comm, mul_left_comm, mul_assoc] using hmain

lemma involInner_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt (fun z : ℂ => z + z ^ 2 / 2)
      (PowerSeries.toFMLS involInnerPS) (0 : ℂ) := by
  have hX : HasFPowerSeriesAt (fun z : ℂ => z)
      (PowerSeries.toFMLS (PowerSeries.X : PowerSeries ℂ)) (0 : ℂ) :=
    hasFPowerSeriesAt_id_toFMLS_X
  have hX2 : HasFPowerSeriesAt (fun z : ℂ => z * z)
      (PowerSeries.toFMLS ((PowerSeries.X : PowerSeries ℂ) ^ 2)) (0 : ℂ) := by
    simpa [pow_two] using hasFPowerSeriesAt_mul_toFMLS hX hX
  have hhalf : HasFPowerSeriesAt (fun z : ℂ => (2⁻¹ : ℂ) • (z * z))
      ((2⁻¹ : ℂ) • PowerSeries.toFMLS ((PowerSeries.X : PowerSeries ℂ) ^ 2)) (0 : ℂ) := by
    simpa using (HasFPowerSeriesAt.const_smul (c := (2⁻¹ : ℂ)) hX2)
  have hsum := hX.add hhalf
  have hseries :
      PowerSeries.toFMLS involInnerPS =
        PowerSeries.toFMLS (PowerSeries.X : PowerSeries ℂ) +
          (2⁻¹ : ℂ) • PowerSeries.toFMLS ((PowerSeries.X : PowerSeries ℂ) ^ 2) := by
    ext n
    simp [involInnerPS, PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars]
  rw [hseries]
  convert hsum using 1
  funext z
  simp [smul_eq_mul]
  ring_nf

lemma involFun_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt involFun involSeries (0 : ℂ) := by
  have houter : HasFPowerSeriesAt Complex.exp (PowerSeries.toFMLS (PowerSeries.exp ℂ))
      ((fun z : ℂ => z + z ^ 2 / 2) 0) := by
    simpa using ExpStirling.expCarrier_hasFPowerSeriesAt_zero
  have hcomp := HasFPowerSeriesAt.comp (g := Complex.exp)
    (f := fun z : ℂ => z + z ^ 2 / 2) houter involInner_hasFPowerSeriesAt_zero
  change HasFPowerSeriesAt involFun (PowerSeries.toFMLS involCarrier) (0 : ℂ)
  rw [involCarrier_eq_complex_subst]
  rw [PowerSeries.toFMLS_subst_eq_comp involInnerPS_constantCoeff]
  simpa [Function.comp_def, involFun, involSeries] using hcomp

/-- Continuous involution saddle mean, `a(r)=r+r^2`. -/
def involSaddleAReal (r : ℝ) : ℝ :=
  r + r ^ 2

/-- Continuous involution saddle variance scale, `b(r)=r+2r^2`. -/
def involSaddleBReal (r : ℝ) : ℝ :=
  r + 2 * r ^ 2

/-- Hayman window for the involution saddle. -/
def involSaddleDeltaReal (r : ℝ) : ℝ :=
  r ^ (-(3 / 4 : ℝ))

@[simp] lemma involSaddleAReal_apply (r : ℝ) :
    involSaddleAReal r = r + r ^ 2 := rfl

@[simp] lemma involSaddleBReal_apply (r : ℝ) :
    involSaddleBReal r = r + 2 * r ^ 2 := rfl

@[simp] lemma involSaddleDeltaReal_apply (r : ℝ) :
    involSaddleDeltaReal r = r ^ (-(3 / 4 : ℝ)) := rfl

/-- The exact exponent left after removing the linear and quadratic saddle terms. -/
def involLocalExponent (r θ : ℝ) : ℂ :=
  (r : ℂ) * ExpStirling.expLocalRemainder θ +
    (((r ^ 2 / 2 : ℝ) : ℂ) * ExpStirling.expLocalRemainder (2 * θ))

lemma complex_two_mul_theta_I (θ : ℝ) :
    (((2 : ℕ) : ℂ) * ((θ : ℂ) * Complex.I)) =
      ((2 * θ : ℝ) : ℂ) * Complex.I := by
  simp [Complex.ofReal_mul, mul_assoc, mul_comm]

lemma complex_theta_I_mul_two (θ : ℝ) :
    (((θ : ℂ) * Complex.I) * ((2 : ℕ) : ℂ)) =
      ((2 * θ : ℝ) : ℂ) * Complex.I := by
  simp [Complex.ofReal_mul, mul_assoc, mul_comm]

lemma invol_saddleLocalRatio_eq (r θ : ℝ) :
    saddleLocalRatio involFun involSaddleAReal involSaddleBReal r θ =
      Complex.exp (involLocalExponent r θ) := by
  unfold saddleLocalRatio involFun involLocalExponent involSaddleAReal involSaddleBReal
  have hsq_full :
      ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ^ 2 =
        ((r ^ 2 : ℝ) : ℂ) * Complex.exp ((2 * θ : ℝ) * Complex.I) := by
    rw [mul_pow, ← Complex.exp_nat_mul]
    rw [show (r : ℂ) ^ 2 = ((r ^ 2 : ℝ) : ℂ) by norm_num]
    rw [show (((2 : ℕ) : ℂ) * ((θ : ℂ) * Complex.I)) =
        ((2 * θ : ℝ) : ℂ) * Complex.I by
      simpa using complex_two_mul_theta_I θ]
  rw [← Complex.exp_sub]
  rw [← Complex.exp_add]
  rw [← Complex.exp_sub]
  congr 1
  rw [ExpStirling.expLocalRemainder_eq θ]
  rw [ExpStirling.expLocalRemainder_eq (2 * θ)]
  rw [hsq_full]
  norm_num [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_pow]
  ring_nf

lemma invol_f_pos_eventually :
    ∀ᶠ r : ℝ in atTop, 0 < (involFun (r : ℂ)).re := by
  refine Eventually.of_forall fun r => ?_
  unfold involFun
  have harg : (r : ℂ) + (r : ℂ) ^ 2 / 2 = ((r + r ^ 2 / 2 : ℝ) : ℂ) := by
    norm_num
  have hval :
      Complex.exp (((r + r ^ 2 / 2 : ℝ) : ℂ)) =
        ((Real.exp (r + r ^ 2 / 2) : ℝ) : ℂ) := by
    simp
  rw [harg, hval]
  exact Real.exp_pos (r + r ^ 2 / 2)

lemma invol_b_pos_eventually :
    ∀ᶠ r : ℝ in atTop, 0 < involSaddleBReal r := by
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  unfold involSaddleBReal
  positivity

lemma invol_delta_pos_eventually :
    ∀ᶠ r : ℝ in atTop, 0 < involSaddleDeltaReal r := by
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  unfold involSaddleDeltaReal
  exact Real.rpow_pos_of_pos hr _

lemma invol_delta_tendsto_zero :
    Tendsto involSaddleDeltaReal atTop (𝓝 0) := by
  simpa [involSaddleDeltaReal] using
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 4))

lemma invol_delta_le_pi_eventually :
    ∀ᶠ r : ℝ in atTop, involSaddleDeltaReal r ≤ Real.pi :=
  invol_delta_tendsto_zero.eventually_le_const Real.pi_pos

lemma invol_delta_le_one_eventually :
    ∀ᶠ r : ℝ in atTop, involSaddleDeltaReal r ≤ 1 :=
  invol_delta_tendsto_zero.eventually_le_const zero_lt_one

lemma invol_delta_mul_r_eq_rpow_eventually :
    (fun r : ℝ => involSaddleDeltaReal r * r) =ᶠ[atTop]
      fun r : ℝ => r ^ (1 / 4 : ℝ) := by
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  calc
    involSaddleDeltaReal r * r
        = r ^ (-(3 / 4 : ℝ)) * r ^ (1 : ℝ) := by
          simp [involSaddleDeltaReal, Real.rpow_one]
    _ = r ^ (-(3 / 4 : ℝ) + (1 : ℝ)) := by
          rw [Real.rpow_add hr]
    _ = r ^ (1 / 4 : ℝ) := by norm_num

lemma invol_delta_sqrt_b_tendsto_atTop :
    Tendsto (fun r : ℝ => involSaddleDeltaReal r * Real.sqrt (involSaddleBReal r))
      atTop atTop := by
  have hpow : Tendsto (fun r : ℝ => r ^ (1 / 4 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)
  refine tendsto_atTop_mono' atTop ?_ hpow
  filter_upwards [eventually_ge_atTop (1 : ℝ), invol_delta_mul_r_eq_rpow_eventually] with
    r hr heq
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  have hb_ge : r ^ 2 ≤ involSaddleBReal r := by
    unfold involSaddleBReal
    nlinarith [sq_nonneg r]
  have hsqrt_ge : r ≤ Real.sqrt (involSaddleBReal r) := by
    exact Real.le_sqrt_of_sq_le hb_ge
  have hδ_nonneg : 0 ≤ involSaddleDeltaReal r := by
    unfold involSaddleDeltaReal
    positivity
  calc
    r ^ (1 / 4 : ℝ) = involSaddleDeltaReal r * r := heq.symm
    _ ≤ involSaddleDeltaReal r * Real.sqrt (involSaddleBReal r) :=
      mul_le_mul_of_nonneg_left hsqrt_ge hδ_nonneg

lemma invol_differentiableOn_eventually :
    ∀ᶠ r : ℝ in atTop,
      DifferentiableOn ℂ involFun (Metric.closedBall (0 : ℂ) r) := by
  refine Eventually.of_forall fun r => ?_
  unfold involFun
  fun_prop

def involLocalControl (r : ℝ) : ℝ :=
  r ^ 2 * (involSaddleDeltaReal r) ^ 3

lemma involLocalControl_eq_rpow_eventually :
    involLocalControl =ᶠ[atTop] fun r : ℝ => r ^ (-(1 / 4 : ℝ)) := by
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  have hr0 : 0 ≤ r := hr.le
  have hr2_rpow : r ^ 2 = r ^ (2 : ℝ) := by
    exact (Real.rpow_natCast r 2).symm
  have hdelta_pow :
      (r ^ (-(3 / 4 : ℝ))) ^ 3 = r ^ (-(3 / 4 : ℝ) * (3 : ℝ)) :=
    (Real.rpow_mul_natCast hr0 (-(3 / 4 : ℝ)) 3).symm
  unfold involLocalControl involSaddleDeltaReal
  calc
    r ^ 2 * (r ^ (-(3 / 4 : ℝ))) ^ 3
        = r ^ (2 : ℝ) * r ^ (-(3 / 4 : ℝ) * (3 : ℝ)) := by
          rw [hr2_rpow, hdelta_pow]
    _ = r ^ ((2 : ℝ) + (-(3 / 4 : ℝ) * (3 : ℝ))) := by
          rw [Real.rpow_add hr]
    _ = r ^ (-(1 / 4 : ℝ)) := by norm_num

lemma involLocalControl_tendsto_zero :
    Tendsto involLocalControl atTop (𝓝 0) := by
  have hpow : Tendsto (fun r : ℝ => r ^ (-(1 / 4 : ℝ))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)
  exact Tendsto.congr' involLocalControl_eq_rpow_eventually.symm hpow

def involLocalConstant : ℝ :=
  40 * Real.exp 2

lemma involLocalConstant_pos : 0 < involLocalConstant := by
  unfold involLocalConstant
  positivity

lemma involLocalBound_tendsto_zero :
    Tendsto (fun r : ℝ => involLocalConstant * involLocalControl r) atTop (𝓝 0) := by
  simpa using involLocalControl_tendsto_zero.const_mul involLocalConstant

lemma expLocalRemainder_norm_le_exp_two {θ : ℝ} (hθ : |θ| ≤ 2) :
    ‖ExpStirling.expLocalRemainder θ‖ ≤ Real.exp 2 * |θ| ^ 3 := by
  calc
    ‖ExpStirling.expLocalRemainder θ‖ ≤ |θ| ^ 3 * Real.exp |θ| :=
      ExpStirling.expLocalRemainder_norm_le θ
    _ ≤ |θ| ^ 3 * Real.exp 2 := by
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hθ)
        (pow_nonneg (abs_nonneg θ) 3)
    _ = Real.exp 2 * |θ| ^ 3 := by ring

lemma invol_local_exponent_norm_le_eventually :
    ∀ᶠ r : ℝ in atTop, ∀ θ : ℝ, |θ| ≤ involSaddleDeltaReal r →
      ‖involLocalExponent r θ‖ ≤ involLocalConstant * involLocalControl r := by
  filter_upwards [eventually_ge_atTop (1 : ℝ), invol_delta_le_one_eventually] with
    r hr hδ_le_one θ hθδ
  let δ : ℝ := involSaddleDeltaReal r
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  have hδ0 : 0 ≤ δ := by
    dsimp [δ, involSaddleDeltaReal]
    positivity
  have hθ_one : |θ| ≤ 1 := hθδ.trans hδ_le_one
  have hθ_two : |θ| ≤ 2 := hθ_one.trans (by norm_num)
  have h2θ_two : |2 * θ| ≤ 2 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [hθ_one]
  have hθ3δ3 : |θ| ^ 3 ≤ δ ^ 3 :=
    pow_le_pow_left₀ (abs_nonneg θ) hθδ 3
  have h2θ3 : |2 * θ| ^ 3 ≤ 8 * δ ^ 3 := by
    calc
      |2 * θ| ^ 3 = 8 * |θ| ^ 3 := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        ring_nf
      _ ≤ 8 * δ ^ 3 := mul_le_mul_of_nonneg_left hθ3δ3 (by norm_num)
  have hrem1 := expLocalRemainder_norm_le_exp_two hθ_two
  have hrem2 := expLocalRemainder_norm_le_exp_two h2θ_two
  have hterm1 :
      ‖(r : ℂ) * ExpStirling.expLocalRemainder θ‖ ≤
        Real.exp 2 * (r * δ ^ 3) := by
    calc
      ‖(r : ℂ) * ExpStirling.expLocalRemainder θ‖
          = r * ‖ExpStirling.expLocalRemainder θ‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
      _ ≤ r * (Real.exp 2 * |θ| ^ 3) :=
        mul_le_mul_of_nonneg_left hrem1 hr0
      _ ≤ r * (Real.exp 2 * δ ^ 3) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hθ3δ3 (Real.exp_pos 2).le) hr0
      _ = Real.exp 2 * (r * δ ^ 3) := by ring_nf
  have hterm2 :
      ‖(((r ^ 2 / 2 : ℝ) : ℂ) * ExpStirling.expLocalRemainder (2 * θ))‖ ≤
        4 * Real.exp 2 * (r ^ 2 * δ ^ 3) := by
    have hcoef0 : 0 ≤ r ^ 2 / 2 := by positivity
    calc
      ‖(((r ^ 2 / 2 : ℝ) : ℂ) * ExpStirling.expLocalRemainder (2 * θ))‖
          = (r ^ 2 / 2) * ‖ExpStirling.expLocalRemainder (2 * θ)‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcoef0]
      _ ≤ (r ^ 2 / 2) * (Real.exp 2 * |2 * θ| ^ 3) :=
        mul_le_mul_of_nonneg_left hrem2 hcoef0
      _ ≤ (r ^ 2 / 2) * (Real.exp 2 * (8 * δ ^ 3)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left h2θ3 (Real.exp_pos 2).le) hcoef0
      _ = 4 * Real.exp 2 * (r ^ 2 * δ ^ 3) := by ring_nf
  have hterm1' :
      Real.exp 2 * (r * δ ^ 3) ≤ Real.exp 2 * (r ^ 2 * δ ^ 3) := by
    have hr_le_r2 : r ≤ r ^ 2 := by nlinarith [hr]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hr_le_r2 (pow_nonneg hδ0 3)) (Real.exp_pos 2).le
  calc
    ‖involLocalExponent r θ‖
        ≤ ‖(r : ℂ) * ExpStirling.expLocalRemainder θ‖ +
          ‖(((r ^ 2 / 2 : ℝ) : ℂ) * ExpStirling.expLocalRemainder (2 * θ))‖ :=
        norm_add_le _ _
    _ ≤ Real.exp 2 * (r * δ ^ 3) + 4 * Real.exp 2 * (r ^ 2 * δ ^ 3) :=
        add_le_add hterm1 hterm2
    _ ≤ Real.exp 2 * (r ^ 2 * δ ^ 3) + 4 * Real.exp 2 * (r ^ 2 * δ ^ 3) :=
        add_le_add hterm1' (le_refl _)
    _ = 5 * Real.exp 2 * (r ^ 2 * δ ^ 3) := by ring_nf
    _ ≤ involLocalConstant * involLocalControl r := by
      unfold involLocalConstant involLocalControl
      dsimp [δ]
      have hnonneg : 0 ≤ r ^ 2 * (r ^ (-(3 / 4 : ℝ))) ^ 3 := by
        positivity
      nlinarith [Real.exp_pos 2, hnonneg]

lemma invol_local_uniform :
    ∀ ε > 0, ∀ᶠ (r : ℝ) in atTop, ∀ θ : ℝ,
      |θ| ≤ involSaddleDeltaReal r →
        ‖saddleLocalRatio involFun involSaddleAReal involSaddleBReal r θ - 1‖ ≤ ε := by
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  have hsmall :
      ∀ᶠ r : ℝ in atTop, involLocalConstant * involLocalControl r ≤ ε / 2 :=
    involLocalBound_tendsto_zero.eventually_le_const hhalf
  have hone :
      ∀ᶠ r : ℝ in atTop, involLocalConstant * involLocalControl r ≤ 1 :=
    involLocalBound_tendsto_zero.eventually_le_const zero_lt_one
  filter_upwards [invol_local_exponent_norm_le_eventually, hsmall, hone] with
    r hloc hsmallr honer θ hθ
  rw [invol_saddleLocalRatio_eq]
  have hz : ‖involLocalExponent r θ‖ ≤ involLocalConstant * involLocalControl r :=
    hloc θ hθ
  have hz_one : ‖involLocalExponent r θ‖ ≤ 1 := hz.trans honer
  calc
    ‖Complex.exp (involLocalExponent r θ) - 1‖
        ≤ 2 * ‖involLocalExponent r θ‖ :=
          Complex.norm_exp_sub_one_le hz_one
    _ ≤ 2 * (involLocalConstant * involLocalControl r) :=
          mul_le_mul_of_nonneg_left hz (by norm_num)
    _ ≤ ε := by linarith

lemma invol_saddleGAt_norm (r : ℝ) (n : ℕ) (θ : ℝ) :
    ‖saddleGAt involFun r n θ‖ =
      Real.exp (r * (Real.cos θ - 1) + (r ^ 2 / 2) * (Real.cos (2 * θ) - 1)) := by
  unfold saddleGAt involFun
  have hphase : ‖Complex.exp (-(↑↑n * ↑θ) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  have hden :
      ‖Complex.exp ((r : ℂ) + (r : ℂ) ^ 2 / 2)‖ =
        Real.exp (r + r ^ 2 / 2) := by
    rw [Complex.norm_exp]
    congr 1
    rw [Complex.add_re]
    have hsq : (((r : ℂ) ^ 2 / 2).re = r ^ 2 / 2) := by
      rw [Complex.div_re]
      have hre : ((r : ℂ) ^ 2).re = r ^ 2 := by
        rw [pow_two, Complex.mul_re]
        simp
        ring
      have him : ((r : ℂ) ^ 2).im = 0 := by
        rw [pow_two, Complex.mul_im]
        simp
      rw [hre, him]
      norm_num [Complex.normSq]
      ring
    rw [hsq]
    simp
  have hnum_re :
      (((r : ℂ) * Complex.exp (θ * Complex.I)) +
          ((r : ℂ) * Complex.exp (θ * Complex.I)) ^ 2 / 2).re =
        r * Real.cos θ + (r ^ 2 / 2) * Real.cos (2 * θ) := by
    have hsq_div :
        ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ^ 2 / 2 =
          (((r ^ 2 / 2 : ℝ) : ℂ) * Complex.exp ((2 * θ : ℝ) * Complex.I)) := by
      have hsq0 :
          ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ^ 2 =
            ((r ^ 2 : ℝ) : ℂ) * Complex.exp ((2 * θ : ℝ) * Complex.I) := by
        rw [mul_pow, ← Complex.exp_nat_mul]
        rw [show (r : ℂ) ^ 2 = ((r ^ 2 : ℝ) : ℂ) by norm_num]
        rw [show (((2 : ℕ) : ℂ) * ((θ : ℂ) * Complex.I)) =
            ((2 * θ : ℝ) : ℂ) * Complex.I by
          simpa using complex_two_mul_theta_I θ]
      rw [hsq0]
      norm_num [Complex.ofReal_mul]
      ring_nf
    rw [hsq_div]
    have hre1 :
        ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)).re = r * Real.cos θ := by
      rw [Complex.exp_ofReal_mul_I]
      simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero]
    have hre2 :
        ((((r ^ 2 / 2 : ℝ) : ℂ) * Complex.exp ((2 * θ : ℝ) * Complex.I)).re =
          (r ^ 2 / 2) * Real.cos (2 * θ)) := by
      rw [Complex.exp_ofReal_mul_I]
      simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero]
    rw [Complex.add_re, hre1, hre2]
  have hnum :
      ‖Complex.exp (((r : ℂ) * Complex.exp (↑θ * Complex.I)) +
          ((r : ℂ) * Complex.exp (↑θ * Complex.I)) ^ 2 / 2)‖ =
        Real.exp (r * Real.cos θ + (r ^ 2 / 2) * Real.cos (2 * θ)) := by
    rw [Complex.norm_exp, hnum_re]
  have hden_pos : 0 < Real.exp (r + r ^ 2 / 2) := Real.exp_pos _
  calc
    ‖Complex.exp (((r : ℂ) * Complex.exp (↑θ * Complex.I)) +
          ((r : ℂ) * Complex.exp (↑θ * Complex.I)) ^ 2 / 2) /
        Complex.exp ((r : ℂ) + (r : ℂ) ^ 2 / 2) *
        Complex.exp (-(↑↑n * ↑θ) * Complex.I)‖
        = Real.exp (r * Real.cos θ + (r ^ 2 / 2) * Real.cos (2 * θ)) /
            Real.exp (r + r ^ 2 / 2) := by
          rw [norm_mul, hphase, mul_one, norm_div, hnum, hden]
    _ = Real.exp (r * (Real.cos θ - 1) +
          (r ^ 2 / 2) * (Real.cos (2 * θ) - 1)) := by
      rw [← Real.exp_sub]
      congr 1
      ring_nf

def involTailE (r : ℝ) : ℝ :=
  Real.exp (-(1 / (2 * Real.pi ^ 2)) * r ^ (1 / 4 : ℝ))

lemma involTailE_nonneg_eventually :
    ∀ᶠ r : ℝ in atTop, 0 ≤ involTailE r :=
  Eventually.of_forall fun r => by
    unfold involTailE
    positivity

lemma involTailE_decay :
    Tendsto (fun r : ℝ => Real.sqrt (2 * Real.pi * involSaddleBReal r) * involTailE r)
      atTop (𝓝 0) := by
  let c : ℝ := 1 / (2 * Real.pi ^ 2)
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hbase :
      Tendsto (fun y : ℝ => y ^ (4 : ℝ) * Real.exp (-c * y)) atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (4 : ℝ) c hc
  have hy : Tendsto (fun r : ℝ => r ^ (1 / 4 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)
  have hcomp :
      Tendsto (fun r : ℝ => (r ^ (1 / 4 : ℝ)) ^ (4 : ℝ) *
        Real.exp (-c * r ^ (1 / 4 : ℝ))) atTop (𝓝 0) :=
    hbase.comp hy
  have hscaled :
      Tendsto (fun r : ℝ => Real.sqrt (6 * Real.pi) *
        ((r ^ (1 / 4 : ℝ)) ^ (4 : ℝ) *
          Real.exp (-c * r ^ (1 / 4 : ℝ)))) atTop (𝓝 0) := by
    simpa using hcomp.const_mul (Real.sqrt (6 * Real.pi))
  refine squeeze_zero' ?_ ?_ hscaled
  · exact Eventually.of_forall fun r => by
      exact mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    have hr0 : 0 ≤ r := le_trans zero_le_one hr
    have hB_le : involSaddleBReal r ≤ 3 * r ^ 2 := by
      unfold involSaddleBReal
      nlinarith [hr]
    have hsqrt :
        Real.sqrt (2 * Real.pi * involSaddleBReal r) ≤
          Real.sqrt (6 * Real.pi) * r := by
      have hmul : 2 * Real.pi * involSaddleBReal r ≤ 6 * Real.pi * r ^ 2 := by
        calc
          2 * Real.pi * involSaddleBReal r
              ≤ 2 * Real.pi * (3 * r ^ 2) :=
                mul_le_mul_of_nonneg_left hB_le (by positivity)
          _ = 6 * Real.pi * r ^ 2 := by ring_nf
      calc
        Real.sqrt (2 * Real.pi * involSaddleBReal r)
            ≤ Real.sqrt (6 * Real.pi * r ^ 2) := Real.sqrt_le_sqrt hmul
        _ = Real.sqrt (6 * Real.pi) * r := by
          have h6pi : 0 ≤ 6 * Real.pi := by positivity
          rw [Real.sqrt_mul h6pi (r ^ 2)]
          rw [Real.sqrt_sq hr0]
    have hrpow4 : (r ^ (1 / 4 : ℝ)) ^ (4 : ℝ) = r := by
      rw [← Real.rpow_mul hr0]
      norm_num [Real.rpow_one]
    calc
      Real.sqrt (2 * Real.pi * involSaddleBReal r) * involTailE r
          ≤ (Real.sqrt (6 * Real.pi) * r) * involTailE r :=
            mul_le_mul_of_nonneg_right hsqrt (by
              unfold involTailE
              positivity)
      _ = Real.sqrt (6 * Real.pi) *
            ((r ^ (1 / 4 : ℝ)) ^ (4 : ℝ) *
              Real.exp (-c * r ^ (1 / 4 : ℝ))) := by
        unfold involTailE
        dsimp [c]
        rw [hrpow4]
        ring_nf

lemma invol_tail_bound_eventually :
    ∀ᶠ r : ℝ in atTop, ∀ n : ℕ, ∀ θ : ℝ,
      involSaddleDeltaReal r ≤ |θ| → |θ| ≤ Real.pi →
        ‖saddleGAt involFun r n θ‖ ≤ involTailE r := by
  let c : ℝ := 1 / (2 * Real.pi ^ 2)
  have hcpos : 0 < c := by
    dsimp [c]
    positivity
  have hc_le_one : c ≤ 1 := by
    dsimp [c]
    have hden : 1 ≤ 2 * Real.pi ^ 2 := by
      nlinarith [Real.two_le_pi]
    have hden_pos : 0 < 2 * Real.pi ^ 2 := by positivity
    rw [div_le_iff₀ hden_pos]
    nlinarith
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr n θ hδθ hθπ
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  have hδ0 : 0 ≤ involSaddleDeltaReal r := by
    unfold involSaddleDeltaReal
    positivity
  rw [invol_saddleGAt_norm]
  unfold involTailE
  apply Real.exp_le_exp.mpr
  have htarget_quarter : c * r ^ (1 / 4 : ℝ) ≤ r := by
    have hpow_le : r ^ (1 / 4 : ℝ) ≤ r := by
      calc
        r ^ (1 / 4 : ℝ) ≤ r ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hr (by norm_num : (1 / 4 : ℝ) ≤ 1)
        _ = r := by rw [Real.rpow_one]
    calc
      c * r ^ (1 / 4 : ℝ) ≤ 1 * r ^ (1 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_right hc_le_one (Real.rpow_nonneg hr0 _)
      _ ≤ r := by simpa using hpow_le
  by_cases hsmall : |θ| ≤ Real.pi / 2
  · have h2θπ : |2 * θ| ≤ Real.pi := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith
    have hcos2 := Real.cos_le_one_sub_mul_cos_sq h2θπ
    have hcos2_sub : Real.cos (2 * θ) - 1 ≤
        -(2 / Real.pi ^ 2) * (2 * θ) ^ 2 := by
      linarith
    have hquad :
        r ^ 2 * (involSaddleDeltaReal r) ^ 2 = r ^ (1 / 2 : ℝ) := by
      have hr2_rpow : r ^ 2 = r ^ (2 : ℝ) := by
        exact (Real.rpow_natCast r 2).symm
      have hdelta_pow :
          (r ^ (-(3 / 4 : ℝ))) ^ 2 = r ^ (-(3 / 4 : ℝ) * (2 : ℝ)) :=
        (Real.rpow_mul_natCast hr0 (-(3 / 4 : ℝ)) 2).symm
      unfold involSaddleDeltaReal
      calc
        r ^ 2 * (r ^ (-(3 / 4 : ℝ))) ^ 2
            = r ^ (2 : ℝ) * r ^ (-(3 / 4 : ℝ) * (2 : ℝ)) := by
              rw [hr2_rpow, hdelta_pow]
        _ = r ^ ((2 : ℝ) + (-(3 / 4 : ℝ) * (2 : ℝ))) := by
              rw [Real.rpow_add (lt_of_lt_of_le zero_lt_one hr)]
        _ = r ^ (1 / 2 : ℝ) := by norm_num
    have hθsq : (involSaddleDeltaReal r) ^ 2 ≤ θ ^ 2 := by
      calc
        (involSaddleDeltaReal r) ^ 2 ≤ |θ| ^ 2 :=
          pow_le_pow_left₀ hδ0 hδθ 2
        _ = θ ^ 2 := by rw [sq_abs]
    have hmain :
        r * (Real.cos θ - 1) + (r ^ 2 / 2) * (Real.cos (2 * θ) - 1)
          ≤ -c * r ^ (1 / 4 : ℝ) := by
      have hcos1_nonpos : Real.cos θ - 1 ≤ 0 := by
        linarith [Real.cos_le_one θ]
      have hleft_nonpos : r * (Real.cos θ - 1) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hr0 hcos1_nonpos
      have hcoef_nonpos : -(4 / Real.pi ^ 2) ≤ 0 := by
        have hpos : 0 ≤ 4 / Real.pi ^ 2 := by positivity
        linarith
      have hquad_lower : r ^ (1 / 4 : ℝ) ≤ r ^ (1 / 2 : ℝ) := by
        exact Real.rpow_le_rpow_of_exponent_le hr (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2)
      have hstrong :
          (r ^ 2 / 2) * (Real.cos (2 * θ) - 1)
            ≤ -(4 / Real.pi ^ 2) * (r ^ 2 * (involSaddleDeltaReal r) ^ 2) := by
        calc
          (r ^ 2 / 2) * (Real.cos (2 * θ) - 1)
              ≤ (r ^ 2 / 2) * (-(2 / Real.pi ^ 2) * (2 * θ) ^ 2) :=
                mul_le_mul_of_nonneg_left hcos2_sub (by positivity)
          _ = -(4 / Real.pi ^ 2) * (r ^ 2 * θ ^ 2) := by ring_nf
          _ ≤ -(4 / Real.pi ^ 2) * (r ^ 2 * (involSaddleDeltaReal r) ^ 2) := by
            exact mul_le_mul_of_nonpos_left
              (mul_le_mul_of_nonneg_left hθsq (sq_nonneg r)) hcoef_nonpos
      have hconst : c * r ^ (1 / 4 : ℝ) ≤
          (4 / Real.pi ^ 2) * (r ^ 2 * (involSaddleDeltaReal r) ^ 2) := by
        rw [hquad]
        have hc4 : c ≤ 4 / Real.pi ^ 2 := by
          dsimp [c]
          field_simp [Real.pi_ne_zero]
          norm_num
        calc
          c * r ^ (1 / 4 : ℝ) ≤ c * r ^ (1 / 2 : ℝ) :=
            mul_le_mul_of_nonneg_left hquad_lower hcpos.le
          _ ≤ (4 / Real.pi ^ 2) * r ^ (1 / 2 : ℝ) :=
            mul_le_mul_of_nonneg_right hc4 (Real.rpow_nonneg hr0 _)
      calc
        r * (Real.cos θ - 1) + (r ^ 2 / 2) * (Real.cos (2 * θ) - 1)
            ≤ 0 + (-(4 / Real.pi ^ 2) *
                (r ^ 2 * (involSaddleDeltaReal r) ^ 2)) :=
              add_le_add hleft_nonpos hstrong
        _ ≤ -c * r ^ (1 / 4 : ℝ) := by linarith
    exact hmain
  · have hlarge : Real.pi / 2 < |θ| := lt_of_not_ge hsmall
    have hcos_nonpos : Real.cos θ ≤ 0 := by
      by_cases hθnonneg : 0 ≤ θ
      · have hθ_le_pi : θ ≤ Real.pi := (abs_le.mp hθπ).2
        have hpi2_le : Real.pi / 2 ≤ θ := by
          have habs_eq : |θ| = θ := abs_of_nonneg hθnonneg
          linarith
        exact Real.cos_nonpos_of_pi_div_two_le_of_le hpi2_le (by linarith [hθ_le_pi])
      · have hθneg : θ < 0 := lt_of_not_ge hθnonneg
        have hneg_le_pi : -θ ≤ Real.pi := by
          have h := (abs_le.mp hθπ).1
          linarith
        have hpi2_le_neg : Real.pi / 2 ≤ -θ := by
          have habs_eq : |θ| = -θ := abs_of_neg hθneg
          linarith
        have hcos := Real.cos_nonpos_of_pi_div_two_le_of_le hpi2_le_neg
          (by linarith [hneg_le_pi])
        simpa [Real.cos_neg] using hcos
    have hcos2_nonpos : Real.cos (2 * θ) - 1 ≤ 0 := by
      linarith [Real.cos_le_one (2 * θ)]
    have hmain :
        r * (Real.cos θ - 1) + (r ^ 2 / 2) * (Real.cos (2 * θ) - 1)
          ≤ -c * r ^ (1 / 4 : ℝ) := by
      have hfirst : r * (Real.cos θ - 1) ≤ -r := by
        have hcos_sub : Real.cos θ - 1 ≤ -1 := by linarith
        calc
          r * (Real.cos θ - 1) ≤ r * (-1) :=
            mul_le_mul_of_nonneg_left hcos_sub hr0
          _ = -r := by ring
      have hsecond : (r ^ 2 / 2) * (Real.cos (2 * θ) - 1) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hcos2_nonpos
      calc
        r * (Real.cos θ - 1) + (r ^ 2 / 2) * (Real.cos (2 * θ) - 1)
            ≤ -r + 0 := add_le_add hfirst hsecond
        _ ≤ -c * r ^ (1 / 4 : ℝ) := by linarith
    exact hmain

lemma invol_tail_uniform :
    ∃ E : ℝ → ℝ,
      (∀ᶠ (r : ℝ) in atTop, 0 ≤ E r) ∧
      Tendsto (fun r : ℝ => Real.sqrt (2 * Real.pi * involSaddleBReal r) * E r)
        atTop (𝓝 0) ∧
      (∀ᶠ (r : ℝ) in atTop, ∀ n : ℕ, ∀ θ : ℝ,
        involSaddleDeltaReal r ≤ |θ| → |θ| ≤ Real.pi →
          ‖saddleGAt involFun r n θ‖ ≤ E r) := by
  exact ⟨involTailE, involTailE_nonneg_eventually, involTailE_decay, invol_tail_bound_eventually⟩

/-- The nonnegative saddle radius solving `r^2+r=n`. -/
def involSaddleRadius (n : ℕ) : ℝ :=
  (Real.sqrt (1 + 4 * (n : ℝ)) - 1) / 2

lemma involSaddleRadius_nonneg (n : ℕ) : 0 ≤ involSaddleRadius n := by
  unfold involSaddleRadius
  have hle : 1 ≤ Real.sqrt (1 + 4 * (n : ℝ)) := by
    have hn0 : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
    have hle' : Real.sqrt (1 : ℝ) ≤ Real.sqrt (1 + 4 * (n : ℝ)) :=
      Real.sqrt_le_sqrt (by nlinarith)
    simpa only [Real.sqrt_one] using hle'
  linarith

lemma involSaddleAReal_radius (n : ℕ) :
    involSaddleAReal (involSaddleRadius n) = (n : ℝ) := by
  unfold involSaddleAReal involSaddleRadius
  have hnonneg : 0 ≤ 1 + 4 * (n : ℝ) := by positivity
  have hs : Real.sqrt (1 + 4 * (n : ℝ)) ^ 2 = 1 + 4 * (n : ℝ) :=
    Real.sq_sqrt hnonneg
  nlinarith

lemma involSaddleAReal_strictMonoOn_nonneg :
    StrictMonoOn involSaddleAReal (Set.Ici (0 : ℝ)) := by
  intro x hx y hy hxy
  unfold involSaddleAReal
  have hpos : 0 < (y - x) * (1 + x + y) := by
    have hdiff : 0 < y - x := sub_pos.mpr hxy
    have hx0 : 0 ≤ x := hx
    have hy0 : 0 ≤ y := hy
    have hsum : 0 < 1 + x + y := by linarith
    exact mul_pos hdiff hsum
  nlinarith

lemma involSaddleRadius_tendsto_atTop :
    Tendsto involSaddleRadius atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro M
  let M0 : ℝ := max M 0
  obtain ⟨N, hN⟩ := exists_nat_gt (involSaddleAReal M0)
  refine ⟨N, fun n hn => ?_⟩
  have hM0_nonneg : 0 ≤ M0 := le_max_right _ _
  have hM_le_M0 : M ≤ M0 := le_max_left _ _
  have hnR : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hAM0_lt_n : involSaddleAReal M0 < (n : ℝ) := hN.trans_le hnR
  by_contra hnot
  have hr_lt_M : involSaddleRadius n < M := lt_of_not_ge hnot
  have hr_lt_M0 : involSaddleRadius n < M0 := hr_lt_M.trans_le hM_le_M0
  have hstrict :
      involSaddleAReal (involSaddleRadius n) < involSaddleAReal M0 :=
    involSaddleAReal_strictMonoOn_nonneg
      (involSaddleRadius_nonneg n) hM0_nonneg hr_lt_M0
  rw [involSaddleAReal_radius] at hstrict
  linarith

def involHAdmissible : HAdmissible involFun involSeries where
  ρ := involSeries.radius
  radFilter := atTop
  a := involSaddleAReal
  b := involSaddleBReal
  δ := involSaddleDeltaReal
  hp := involFun_hasFPowerSeriesAt_zero
  radius_eq := rfl
  radius_pos := by
    simpa [involSeries] using involFun_hasFPowerSeriesAt_zero.radius_pos
  rad_neBot := by infer_instance
  r_pos := eventually_gt_atTop (0 : ℝ)
  differentiableOn := invol_differentiableOn_eventually
  f_pos := invol_f_pos_eventually
  b_pos := invol_b_pos_eventually
  δ_pos := invol_delta_pos_eventually
  δ_le_pi := invol_delta_le_pi_eventually
  δ_sqrt_b_tendsto_atTop := invol_delta_sqrt_b_tendsto_atTop
  local_uniform := invol_local_uniform
  tail_uniform := invol_tail_uniform

def involHAdmissibleSaddleSequence : SaddleSequence involHAdmissible where
  r := involSaddleRadius
  tendsTo := by
    simpa [involHAdmissible] using involSaddleRadius_tendsto_atTop
  saddle_eq := by
    exact Eventually.of_forall fun n => by
      change involSaddleAReal (involSaddleRadius n) = (n : ℝ)
      exact involSaddleAReal_radius n

theorem invol_coeff_isEquivalent_saddle_from_HAdmissible :
    (fun n : ℕ => involSeries.coeff n) ~[atTop]
      (fun n : ℕ => saddleScale involFun involSaddleRadius
        (fun n => involSaddleBReal (involSaddleRadius n)) n) := by
  have h := coeff_isEquivalent_saddle involHAdmissible involHAdmissibleSaddleSequence
  simpa [HAdmissible.B, involHAdmissibleSaddleSequence, involHAdmissible] using h

theorem involution_count_over_factorial_isEquivalent_saddle :
    (fun n : ℕ =>
      (((AnalyticCombinatorics.Ch1.CombClass.parts12.set.counts n : ℝ) / n.factorial : ℝ) : ℂ))
      ~[atTop]
      (fun n : ℕ => saddleScale involFun involSaddleRadius
        (fun n => involSaddleBReal (involSaddleRadius n)) n) := by
  simpa [involSeries, PowerSeries.coeff_toFMLS, involCarrier_coeff, involCoeffR] using
    invol_coeff_isEquivalent_saddle_from_HAdmissible

theorem involution_count_isEquivalent_factorial_mul_saddle :
    (fun n : ℕ =>
      ((AnalyticCombinatorics.Ch1.CombClass.parts12.set.counts n : ℝ) : ℂ))
      ~[atTop]
      (fun n : ℕ => ((n.factorial : ℝ) : ℂ) *
        saddleScale involFun involSaddleRadius
          (fun n => involSaddleBReal (involSaddleRadius n)) n) := by
  have hfact :
      (fun n : ℕ => ((n.factorial : ℝ) : ℂ)) ~[atTop]
        (fun n : ℕ => ((n.factorial : ℝ) : ℂ)) :=
    Asymptotics.IsEquivalent.refl
  have h := hfact.mul involution_count_over_factorial_isEquivalent_saddle
  refine h.congr_left ?_
  refine Eventually.of_forall fun n => ?_
  have hfact_ne : ((n.factorial : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_ne_zero n)
  change ((n.factorial : ℝ) : ℂ) *
      (((AnalyticCombinatorics.Ch1.CombClass.parts12.set.counts n : ℝ) /
        n.factorial : ℝ) : ℂ) =
    ((AnalyticCombinatorics.Ch1.CombClass.parts12.set.counts n : ℝ) : ℂ)
  norm_num [Complex.ofReal_div]
  field_simp [hfact_ne]
  exact mul_div_cancel_left₀
    (((AnalyticCombinatorics.Ch1.CombClass.parts12.set.counts n : ℝ) : ℂ)) hfact_ne

end InvolutionHAdmissible
