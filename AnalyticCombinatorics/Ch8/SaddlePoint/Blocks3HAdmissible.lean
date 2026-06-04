import Mathlib
import AnalyticCombinatorics.Ch8.SaddlePoint.HAdmissible
import AnalyticCombinatorics.Ch8.SaddlePoint.InvolutionHAdmissible
import AnalyticCombinatorics.Ch8.SaddlePoint.ExpStirling
import AnalyticCombinatorics.Ch2.EGF.Applications
import AnalyticCombinatorics.Ch4.Analytic.SubstComp

/-!
# Blocks of size at most three: H-admissible saddle data

This file records the Hayman data for the EGF
`exp (z + z^2/2 + z^3/6)`, the labelled SET class whose components have
sizes `1`, `2`, or `3`.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval PowerSeries

noncomputable section

namespace AnalyticCombinatorics.Ch1

open PowerSeries

/-- The class with one component of each size `1`, `2`, and `3`. -/
def CombClass.parts123 : CombClass where
  Obj n := Fin (if n = 1 then 1 else if n = 2 then 1 else if n = 3 then 1 else 0)
  finObj _ := inferInstance

@[simp] lemma CombClass.counts_parts123 (n : ℕ) :
    CombClass.parts123.counts n =
      if n = 1 then 1 else if n = 2 then 1 else if n = 3 then 1 else 0 :=
  Fintype.card_fin _

/-- The EGF of the size-`1`, `2`, `3` component class is `z + z^2/2 + z^3/6`. -/
theorem CombClass.egf_parts123_egf :
    CombClass.parts123.egf =
      X + (2⁻¹ : ℚ) • X ^ 2 + (6⁻¹ : ℚ) • X ^ 3 := by
  ext n
  rw [CombClass.coeff_egf, CombClass.counts_parts123, map_add, map_add, coeff_X,
    map_smul, map_smul, coeff_X_pow, coeff_X_pow, smul_eq_mul, smul_eq_mul]
  by_cases h1 : n = 1
  · subst n
    norm_num [Nat.factorial]
  by_cases h2 : n = 2
  · subst n
    norm_num [Nat.factorial]
  by_cases h3 : n = 3
  · subst n
    norm_num [Nat.factorial]
  simp [h1, h2, h3]

/-- Set partitions whose blocks have size at most `3`: `SET(parts123)`. -/
abbrev CombClass.blocks3 : CombClass :=
  CombClass.parts123.set

/-- The EGF of set partitions into blocks of size at most `3`. -/
theorem CombClass.egf_blocks3 :
    CombClass.blocks3.egf =
      (PowerSeries.exp ℚ).subst
        (X + (2⁻¹ : ℚ) • X ^ 2 + (6⁻¹ : ℚ) • X ^ 3) := by
  rw [CombClass.egf_set _ (by simp [CombClass.counts_parts123]),
    CombClass.egf_parts123_egf]

end AnalyticCombinatorics.Ch1

namespace Blocks3HAdmissible

abbrev blocks3CoeffR (n : ℕ) : ℝ :=
  (AnalyticCombinatorics.Ch1.CombClass.blocks3.counts n : ℝ) / n.factorial

lemma blocks3CoeffR_nonneg (n : ℕ) : 0 ≤ blocks3CoeffR n := by
  positivity

/-- The genuine complex EGF carrier from the Ch2 labelled SET construction. -/
def blocks3Carrier : PowerSeries ℂ :=
  PowerSeries.mapℂ AnalyticCombinatorics.Ch1.CombClass.blocks3.egf

@[simp] theorem blocks3Carrier_coeff (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n blocks3Carrier = (blocks3CoeffR n : ℂ) := by
  simp [blocks3Carrier, blocks3CoeffR, AnalyticCombinatorics.Ch1.CombClass.coeff_egf]

/-- The formal series used by the H-admissible interface. -/
noncomputable abbrev blocks3Series : FormalMultilinearSeries ℂ ℂ ℂ :=
  PowerSeries.toFMLS blocks3Carrier

/-- The analytic function `exp (z + z^2/2 + z^3/6)`. -/
abbrev blocks3Fun (z : ℂ) : ℂ :=
  Complex.exp (z + z ^ 2 / 2 + z ^ 3 / 6)

/-- The cubic inner PowerSeries `z + z^2/2 + z^3/6`. -/
def blocks3InnerPS : PowerSeries ℂ :=
  (PowerSeries.X : PowerSeries ℂ) +
    (2⁻¹ : ℂ) • (PowerSeries.X : PowerSeries ℂ) ^ 2 +
      (6⁻¹ : ℂ) • (PowerSeries.X : PowerSeries ℂ) ^ 3

lemma blocks3InnerPS_constantCoeff : PowerSeries.constantCoeff blocks3InnerPS = 0 := by
  simp [blocks3InnerPS]

theorem blocks3Carrier_eq_complex_subst :
    blocks3Carrier = (PowerSeries.exp ℂ).subst blocks3InnerPS := by
  rw [blocks3Carrier, AnalyticCombinatorics.Ch1.CombClass.egf_blocks3]
  have hsubst : PowerSeries.HasSubst
      ((PowerSeries.X : PowerSeries ℚ) +
        (2⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 2 +
          (6⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 3) := by
    apply PowerSeries.HasSubst.of_constantCoeff_zero'
    simp
  have hmap_inner :
      (((PowerSeries.X : PowerSeries ℚ) +
          (2⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 2 +
            (6⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 3).map
          (algebraMap ℚ ℂ)) =
        blocks3InnerPS := by
    ext n
    by_cases h1 : n = 1
    · subst n
      norm_num [blocks3InnerPS, PowerSeries.coeff_map, PowerSeries.coeff_X_pow]
    by_cases h2 : n = 2
    · subst n
      norm_num [blocks3InnerPS, PowerSeries.coeff_map, PowerSeries.coeff_X_pow]
    by_cases h3 : n = 3
    · subst n
      norm_num [blocks3InnerPS, PowerSeries.coeff_map, PowerSeries.coeff_X_pow]
    simp [blocks3InnerPS, PowerSeries.coeff_map, PowerSeries.coeff_X_pow, h2, h3,
      add_assoc]
  have hmap_exp :
      (PowerSeries.exp ℚ).map (algebraMap ℚ ℂ) = PowerSeries.exp ℂ := by
    ext n
    simp
  change (((PowerSeries.exp ℚ).subst
        ((PowerSeries.X : PowerSeries ℚ) +
          (2⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 2 +
            (6⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 3)).map
      (algebraMap ℚ ℂ)) = _
  rw [PowerSeries.map_subst
    (a := ((PowerSeries.X : PowerSeries ℚ) +
      (2⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 2 +
        (6⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 3))
    (h := algebraMap ℚ ℂ) hsubst (PowerSeries.exp ℚ)]
  rw [hmap_exp]
  change (PowerSeries.exp ℂ).subst
      ((((PowerSeries.X : PowerSeries ℚ) +
        (2⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 2 +
          (6⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 3).map
          (algebraMap ℚ ℂ))) =
    (PowerSeries.exp ℂ).subst blocks3InnerPS
  rw [hmap_inner]

lemma blocks3Inner_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt (fun z : ℂ => z + z ^ 2 / 2 + z ^ 3 / 6)
      (PowerSeries.toFMLS blocks3InnerPS) (0 : ℂ) := by
  have hX : HasFPowerSeriesAt (fun z : ℂ => z)
      (PowerSeries.toFMLS (PowerSeries.X : PowerSeries ℂ)) (0 : ℂ) :=
    InvolutionHAdmissible.hasFPowerSeriesAt_id_toFMLS_X
  have hX2 : HasFPowerSeriesAt (fun z : ℂ => z * z)
      (PowerSeries.toFMLS ((PowerSeries.X : PowerSeries ℂ) ^ 2)) (0 : ℂ) := by
    simpa [pow_two] using InvolutionHAdmissible.hasFPowerSeriesAt_mul_toFMLS hX hX
  have hX3 : HasFPowerSeriesAt (fun z : ℂ => (z * z) * z)
      (PowerSeries.toFMLS ((PowerSeries.X : PowerSeries ℂ) ^ 3)) (0 : ℂ) := by
    have hmul := InvolutionHAdmissible.hasFPowerSeriesAt_mul_toFMLS hX2 hX
    simpa [pow_succ, pow_two, mul_assoc] using hmul
  have hhalf : HasFPowerSeriesAt (fun z : ℂ => (2⁻¹ : ℂ) • (z * z))
      ((2⁻¹ : ℂ) • PowerSeries.toFMLS ((PowerSeries.X : PowerSeries ℂ) ^ 2))
      (0 : ℂ) := by
    simpa using (HasFPowerSeriesAt.const_smul (c := (2⁻¹ : ℂ)) hX2)
  have hsixth : HasFPowerSeriesAt (fun z : ℂ => (6⁻¹ : ℂ) • ((z * z) * z))
      ((6⁻¹ : ℂ) • PowerSeries.toFMLS ((PowerSeries.X : PowerSeries ℂ) ^ 3))
      (0 : ℂ) := by
    simpa using (HasFPowerSeriesAt.const_smul (c := (6⁻¹ : ℂ)) hX3)
  have hsum := (hX.add hhalf).add hsixth
  have hseries :
      PowerSeries.toFMLS blocks3InnerPS =
        PowerSeries.toFMLS (PowerSeries.X : PowerSeries ℂ) +
          (2⁻¹ : ℂ) • PowerSeries.toFMLS ((PowerSeries.X : PowerSeries ℂ) ^ 2) +
            (6⁻¹ : ℂ) • PowerSeries.toFMLS ((PowerSeries.X : PowerSeries ℂ) ^ 3) := by
    ext n
    simp [blocks3InnerPS, PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars]
  rw [hseries]
  convert hsum using 1
  funext z
  simp [smul_eq_mul]
  ring_nf

lemma blocks3Fun_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt blocks3Fun blocks3Series (0 : ℂ) := by
  have houter : HasFPowerSeriesAt Complex.exp (PowerSeries.toFMLS (PowerSeries.exp ℂ))
      ((fun z : ℂ => z + z ^ 2 / 2 + z ^ 3 / 6) 0) := by
    simpa using ExpStirling.expCarrier_hasFPowerSeriesAt_zero
  have hcomp := HasFPowerSeriesAt.comp (g := Complex.exp)
    (f := fun z : ℂ => z + z ^ 2 / 2 + z ^ 3 / 6)
    houter blocks3Inner_hasFPowerSeriesAt_zero
  change HasFPowerSeriesAt blocks3Fun (PowerSeries.toFMLS blocks3Carrier) (0 : ℂ)
  rw [blocks3Carrier_eq_complex_subst]
  rw [PowerSeries.toFMLS_subst_eq_comp blocks3InnerPS_constantCoeff]
  simpa [Function.comp_def, blocks3Fun, blocks3Series] using hcomp

/-- Continuous saddle mean, `a(r)=r+r^2+r^3/2`. -/
def blocks3SaddleAReal (r : ℝ) : ℝ :=
  r + r ^ 2 + r ^ 3 / 2

/-- Continuous saddle variance scale, `b(r)=r+2r^2+3r^3/2`. -/
def blocks3SaddleBReal (r : ℝ) : ℝ :=
  r + 2 * r ^ 2 + 3 * r ^ 3 / 2

/-- Hayman window for the cubic polynomial saddle. -/
def blocks3SaddleDeltaReal (r : ℝ) : ℝ :=
  r ^ (-(7 / 6 : ℝ))

@[simp] lemma blocks3SaddleAReal_apply (r : ℝ) :
    blocks3SaddleAReal r = r + r ^ 2 + r ^ 3 / 2 := rfl

@[simp] lemma blocks3SaddleBReal_apply (r : ℝ) :
    blocks3SaddleBReal r = r + 2 * r ^ 2 + 3 * r ^ 3 / 2 := rfl

@[simp] lemma blocks3SaddleDeltaReal_apply (r : ℝ) :
    blocks3SaddleDeltaReal r = r ^ (-(7 / 6 : ℝ)) := rfl

/-- The exact exponent left after removing the linear and quadratic saddle terms. -/
def blocks3LocalExponent (r θ : ℝ) : ℂ :=
  (r : ℂ) * ExpStirling.expLocalRemainder θ +
    (((r ^ 2 / 2 : ℝ) : ℂ) * ExpStirling.expLocalRemainder (2 * θ)) +
      (((r ^ 3 / 6 : ℝ) : ℂ) * ExpStirling.expLocalRemainder (3 * θ))

lemma complex_two_mul_theta_I (θ : ℝ) :
    (((2 : ℕ) : ℂ) * ((θ : ℂ) * Complex.I)) =
      ((2 * θ : ℝ) : ℂ) * Complex.I := by
  simp [Complex.ofReal_mul, mul_assoc, mul_comm]

lemma complex_three_mul_theta_I (θ : ℝ) :
    (((3 : ℕ) : ℂ) * ((θ : ℂ) * Complex.I)) =
      ((3 * θ : ℝ) : ℂ) * Complex.I := by
  simp [Complex.ofReal_mul, mul_assoc, mul_comm]

lemma blocks3_saddleLocalRatio_eq (r θ : ℝ) :
    saddleLocalRatio blocks3Fun blocks3SaddleAReal blocks3SaddleBReal r θ =
      Complex.exp (blocks3LocalExponent r θ) := by
  unfold saddleLocalRatio blocks3Fun blocks3LocalExponent blocks3SaddleAReal blocks3SaddleBReal
  have hsq_full :
      ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ^ 2 =
        ((r ^ 2 : ℝ) : ℂ) * Complex.exp ((2 * θ : ℝ) * Complex.I) := by
    rw [mul_pow, ← Complex.exp_nat_mul]
    rw [show (r : ℂ) ^ 2 = ((r ^ 2 : ℝ) : ℂ) by norm_num]
    rw [show (((2 : ℕ) : ℂ) * ((θ : ℂ) * Complex.I)) =
        ((2 * θ : ℝ) : ℂ) * Complex.I by
      simpa using complex_two_mul_theta_I θ]
  have hcube_full :
      ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ^ 3 =
        ((r ^ 3 : ℝ) : ℂ) * Complex.exp ((3 * θ : ℝ) * Complex.I) := by
    rw [mul_pow, ← Complex.exp_nat_mul]
    rw [show (r : ℂ) ^ 3 = ((r ^ 3 : ℝ) : ℂ) by norm_num]
    rw [show (((3 : ℕ) : ℂ) * ((θ : ℂ) * Complex.I)) =
        ((3 * θ : ℝ) : ℂ) * Complex.I by
      simpa using complex_three_mul_theta_I θ]
  rw [← Complex.exp_sub]
  rw [← Complex.exp_add]
  rw [← Complex.exp_sub]
  congr 1
  rw [ExpStirling.expLocalRemainder_eq θ]
  rw [ExpStirling.expLocalRemainder_eq (2 * θ)]
  rw [ExpStirling.expLocalRemainder_eq (3 * θ)]
  rw [hsq_full, hcube_full]
  norm_num [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_pow]
  ring_nf

lemma blocks3_f_pos_eventually :
    ∀ᶠ r : ℝ in atTop, 0 < (blocks3Fun (r : ℂ)).re := by
  refine Eventually.of_forall fun r => ?_
  unfold blocks3Fun
  have harg :
      (r : ℂ) + (r : ℂ) ^ 2 / 2 + (r : ℂ) ^ 3 / 6 =
        ((r + r ^ 2 / 2 + r ^ 3 / 6 : ℝ) : ℂ) := by
    norm_num
  have hval :
      Complex.exp (((r + r ^ 2 / 2 + r ^ 3 / 6 : ℝ) : ℂ)) =
        ((Real.exp (r + r ^ 2 / 2 + r ^ 3 / 6) : ℝ) : ℂ) := by
    simp
  rw [harg, hval]
  exact Real.exp_pos (r + r ^ 2 / 2 + r ^ 3 / 6)

lemma blocks3_b_pos_eventually :
    ∀ᶠ r : ℝ in atTop, 0 < blocks3SaddleBReal r := by
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  unfold blocks3SaddleBReal
  positivity

lemma blocks3_delta_pos_eventually :
    ∀ᶠ r : ℝ in atTop, 0 < blocks3SaddleDeltaReal r := by
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  unfold blocks3SaddleDeltaReal
  exact Real.rpow_pos_of_pos hr _

lemma blocks3_delta_tendsto_zero :
    Tendsto blocks3SaddleDeltaReal atTop (𝓝 0) := by
  simpa [blocks3SaddleDeltaReal] using
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 7 / 6))

lemma blocks3_delta_le_pi_eventually :
    ∀ᶠ r : ℝ in atTop, blocks3SaddleDeltaReal r ≤ Real.pi :=
  blocks3_delta_tendsto_zero.eventually_le_const Real.pi_pos

lemma blocks3_delta_le_one_eventually :
    ∀ᶠ r : ℝ in atTop, blocks3SaddleDeltaReal r ≤ 1 :=
  blocks3_delta_tendsto_zero.eventually_le_const zero_lt_one

lemma blocks3_delta_mul_rpow_three_halves_eventually :
    (fun r : ℝ => blocks3SaddleDeltaReal r * r ^ (3 / 2 : ℝ)) =ᶠ[atTop]
      fun r : ℝ => r ^ (1 / 3 : ℝ) := by
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  calc
    blocks3SaddleDeltaReal r * r ^ (3 / 2 : ℝ)
        = r ^ (-(7 / 6 : ℝ)) * r ^ (3 / 2 : ℝ) := by
          simp [blocks3SaddleDeltaReal]
    _ = r ^ (-(7 / 6 : ℝ) + (3 / 2 : ℝ)) := by
          rw [Real.rpow_add hr]
    _ = r ^ (1 / 3 : ℝ) := by norm_num

lemma blocks3_delta_sqrt_b_tendsto_atTop :
    Tendsto (fun r : ℝ => blocks3SaddleDeltaReal r * Real.sqrt (blocks3SaddleBReal r))
      atTop atTop := by
  have hpow : Tendsto (fun r : ℝ => r ^ (1 / 3 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)
  refine tendsto_atTop_mono' atTop ?_ hpow
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    blocks3_delta_mul_rpow_three_halves_eventually] with r hr heq
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  have hb_ge : r ^ 3 ≤ blocks3SaddleBReal r := by
    unfold blocks3SaddleBReal
    nlinarith [sq_nonneg r, mul_nonneg (sq_nonneg r) hr0]
  have hrpow_sq : (r ^ (3 / 2 : ℝ)) ^ 2 = r ^ 3 := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hr0]
    norm_num
  have hsqrt_ge : r ^ (3 / 2 : ℝ) ≤ Real.sqrt (blocks3SaddleBReal r) := by
    exact Real.le_sqrt_of_sq_le (by simpa [hrpow_sq] using hb_ge)
  have hδ_nonneg : 0 ≤ blocks3SaddleDeltaReal r := by
    unfold blocks3SaddleDeltaReal
    positivity
  calc
    r ^ (1 / 3 : ℝ) =
        blocks3SaddleDeltaReal r * r ^ (3 / 2 : ℝ) := heq.symm
    _ ≤ blocks3SaddleDeltaReal r * Real.sqrt (blocks3SaddleBReal r) :=
      mul_le_mul_of_nonneg_left hsqrt_ge hδ_nonneg

lemma blocks3_differentiableOn_eventually :
    ∀ᶠ r : ℝ in atTop,
      DifferentiableOn ℂ blocks3Fun (Metric.closedBall (0 : ℂ) r) := by
  refine Eventually.of_forall fun r => ?_
  unfold blocks3Fun
  fun_prop

def blocks3LocalControl (r : ℝ) : ℝ :=
  r ^ 3 * (blocks3SaddleDeltaReal r) ^ 3

lemma blocks3LocalControl_eq_rpow_eventually :
    blocks3LocalControl =ᶠ[atTop] fun r : ℝ => r ^ (-(1 / 2 : ℝ)) := by
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  have hr0 : 0 ≤ r := hr.le
  have hr3_rpow : r ^ 3 = r ^ (3 : ℝ) := by
    exact (Real.rpow_natCast r 3).symm
  have hdelta_pow :
      (r ^ (-(7 / 6 : ℝ))) ^ 3 = r ^ (-(7 / 6 : ℝ) * (3 : ℝ)) :=
    (Real.rpow_mul_natCast hr0 (-(7 / 6 : ℝ)) 3).symm
  unfold blocks3LocalControl blocks3SaddleDeltaReal
  calc
    r ^ 3 * (r ^ (-(7 / 6 : ℝ))) ^ 3
        = r ^ (3 : ℝ) * r ^ (-(7 / 6 : ℝ) * (3 : ℝ)) := by
          rw [hr3_rpow, hdelta_pow]
    _ = r ^ ((3 : ℝ) + (-(7 / 6 : ℝ) * (3 : ℝ))) := by
          rw [Real.rpow_add hr]
    _ = r ^ (-(1 / 2 : ℝ)) := by norm_num

lemma blocks3LocalControl_tendsto_zero :
    Tendsto blocks3LocalControl atTop (𝓝 0) := by
  have hpow : Tendsto (fun r : ℝ => r ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)
  exact Tendsto.congr' blocks3LocalControl_eq_rpow_eventually.symm hpow

def blocks3LocalConstant : ℝ :=
  100 * Real.exp 3

lemma blocks3LocalConstant_pos : 0 < blocks3LocalConstant := by
  unfold blocks3LocalConstant
  positivity

lemma blocks3LocalBound_tendsto_zero :
    Tendsto (fun r : ℝ => blocks3LocalConstant * blocks3LocalControl r) atTop (𝓝 0) := by
  simpa using blocks3LocalControl_tendsto_zero.const_mul blocks3LocalConstant

lemma expLocalRemainder_norm_le_exp_three {θ : ℝ} (hθ : |θ| ≤ 3) :
    ‖ExpStirling.expLocalRemainder θ‖ ≤ Real.exp 3 * |θ| ^ 3 := by
  calc
    ‖ExpStirling.expLocalRemainder θ‖ ≤ |θ| ^ 3 * Real.exp |θ| :=
      ExpStirling.expLocalRemainder_norm_le θ
    _ ≤ |θ| ^ 3 * Real.exp 3 := by
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hθ)
        (pow_nonneg (abs_nonneg θ) 3)
    _ = Real.exp 3 * |θ| ^ 3 := by ring

lemma blocks3_local_exponent_norm_le_eventually :
    ∀ᶠ r : ℝ in atTop, ∀ θ : ℝ, |θ| ≤ blocks3SaddleDeltaReal r →
      ‖blocks3LocalExponent r θ‖ ≤ blocks3LocalConstant * blocks3LocalControl r := by
  filter_upwards [eventually_ge_atTop (1 : ℝ), blocks3_delta_le_one_eventually] with
    r hr hδ_le_one θ hθδ
  let δ : ℝ := blocks3SaddleDeltaReal r
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  have hδ0 : 0 ≤ δ := by
    dsimp [δ, blocks3SaddleDeltaReal]
    positivity
  have hθ_one : |θ| ≤ 1 := hθδ.trans hδ_le_one
  have hθ_three : |θ| ≤ 3 := hθ_one.trans (by norm_num)
  have h2θ_three : |2 * θ| ≤ 3 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [hθ_one]
  have h3θ_three : |3 * θ| ≤ 3 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    nlinarith [hθ_one]
  have hθ3δ3 : |θ| ^ 3 ≤ δ ^ 3 :=
    pow_le_pow_left₀ (abs_nonneg θ) hθδ 3
  have h2θ3 : |2 * θ| ^ 3 ≤ 8 * δ ^ 3 := by
    calc
      |2 * θ| ^ 3 = 8 * |θ| ^ 3 := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        ring_nf
      _ ≤ 8 * δ ^ 3 := mul_le_mul_of_nonneg_left hθ3δ3 (by norm_num)
  have h3θ3 : |3 * θ| ^ 3 ≤ 27 * δ ^ 3 := by
    calc
      |3 * θ| ^ 3 = 27 * |θ| ^ 3 := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
        ring_nf
      _ ≤ 27 * δ ^ 3 := mul_le_mul_of_nonneg_left hθ3δ3 (by norm_num)
  have hrem1 := expLocalRemainder_norm_le_exp_three hθ_three
  have hrem2 := expLocalRemainder_norm_le_exp_three h2θ_three
  have hrem3 := expLocalRemainder_norm_le_exp_three h3θ_three
  have hterm1 :
      ‖(r : ℂ) * ExpStirling.expLocalRemainder θ‖ ≤
        Real.exp 3 * (r * δ ^ 3) := by
    calc
      ‖(r : ℂ) * ExpStirling.expLocalRemainder θ‖
          = r * ‖ExpStirling.expLocalRemainder θ‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
      _ ≤ r * (Real.exp 3 * |θ| ^ 3) :=
        mul_le_mul_of_nonneg_left hrem1 hr0
      _ ≤ r * (Real.exp 3 * δ ^ 3) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hθ3δ3 (Real.exp_pos 3).le) hr0
      _ = Real.exp 3 * (r * δ ^ 3) := by ring_nf
  have hterm2 :
      ‖(((r ^ 2 / 2 : ℝ) : ℂ) * ExpStirling.expLocalRemainder (2 * θ))‖ ≤
        4 * Real.exp 3 * (r ^ 2 * δ ^ 3) := by
    have hcoef0 : 0 ≤ r ^ 2 / 2 := by positivity
    calc
      ‖(((r ^ 2 / 2 : ℝ) : ℂ) * ExpStirling.expLocalRemainder (2 * θ))‖
          = (r ^ 2 / 2) * ‖ExpStirling.expLocalRemainder (2 * θ)‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcoef0]
      _ ≤ (r ^ 2 / 2) * (Real.exp 3 * |2 * θ| ^ 3) :=
        mul_le_mul_of_nonneg_left hrem2 hcoef0
      _ ≤ (r ^ 2 / 2) * (Real.exp 3 * (8 * δ ^ 3)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left h2θ3 (Real.exp_pos 3).le) hcoef0
      _ = 4 * Real.exp 3 * (r ^ 2 * δ ^ 3) := by ring_nf
  have hterm3 :
      ‖(((r ^ 3 / 6 : ℝ) : ℂ) * ExpStirling.expLocalRemainder (3 * θ))‖ ≤
        (9 / 2) * Real.exp 3 * (r ^ 3 * δ ^ 3) := by
    have hcoef0 : 0 ≤ r ^ 3 / 6 := by positivity
    calc
      ‖(((r ^ 3 / 6 : ℝ) : ℂ) * ExpStirling.expLocalRemainder (3 * θ))‖
          = (r ^ 3 / 6) * ‖ExpStirling.expLocalRemainder (3 * θ)‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcoef0]
      _ ≤ (r ^ 3 / 6) * (Real.exp 3 * |3 * θ| ^ 3) :=
        mul_le_mul_of_nonneg_left hrem3 hcoef0
      _ ≤ (r ^ 3 / 6) * (Real.exp 3 * (27 * δ ^ 3)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left h3θ3 (Real.exp_pos 3).le) hcoef0
      _ = (9 / 2) * Real.exp 3 * (r ^ 3 * δ ^ 3) := by ring_nf
  have hterm1' :
      Real.exp 3 * (r * δ ^ 3) ≤ Real.exp 3 * (r ^ 3 * δ ^ 3) := by
    have one_le_r2 : 1 ≤ r ^ 2 := by nlinarith [hr, sq_nonneg (r - 1)]
    have hr_le_r3 : r ≤ r ^ 3 := by
      calc
        r = r * 1 := by ring
        _ ≤ r * r ^ 2 := mul_le_mul_of_nonneg_left one_le_r2 hr0
        _ = r ^ 3 := by ring
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hr_le_r3 (pow_nonneg hδ0 3)) (Real.exp_pos 3).le
  have hterm2' :
      4 * Real.exp 3 * (r ^ 2 * δ ^ 3) ≤
        4 * Real.exp 3 * (r ^ 3 * δ ^ 3) := by
    have hr2_le_r3 : r ^ 2 ≤ r ^ 3 := by
      calc
        r ^ 2 = r ^ 2 * 1 := by ring
        _ ≤ r ^ 2 * r := mul_le_mul_of_nonneg_left hr (sq_nonneg r)
        _ = r ^ 3 := by ring
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hr2_le_r3 (pow_nonneg hδ0 3))
      (by positivity)
  calc
    ‖blocks3LocalExponent r θ‖
        ≤ ‖(r : ℂ) * ExpStirling.expLocalRemainder θ‖ +
          ‖(((r ^ 2 / 2 : ℝ) : ℂ) * ExpStirling.expLocalRemainder (2 * θ))‖ +
            ‖(((r ^ 3 / 6 : ℝ) : ℂ) * ExpStirling.expLocalRemainder (3 * θ))‖ := by
        let A : ℂ := (r : ℂ) * ExpStirling.expLocalRemainder θ
        let B : ℂ := (((r ^ 2 / 2 : ℝ) : ℂ) * ExpStirling.expLocalRemainder (2 * θ))
        let C : ℂ := (((r ^ 3 / 6 : ℝ) : ℂ) * ExpStirling.expLocalRemainder (3 * θ))
        change ‖A + B + C‖ ≤ ‖A‖ + ‖B‖ + ‖C‖
        calc
          ‖A + B + C‖ ≤ ‖A + B‖ + ‖C‖ := norm_add_le _ _
          _ ≤ (‖A‖ + ‖B‖) + ‖C‖ :=
            by
              simpa [add_comm, add_left_comm, add_assoc] using
                add_le_add_right (norm_add_le A B) ‖C‖
          _ = ‖A‖ + ‖B‖ + ‖C‖ := by ring
    _ ≤ Real.exp 3 * (r * δ ^ 3) +
          4 * Real.exp 3 * (r ^ 2 * δ ^ 3) +
            (9 / 2) * Real.exp 3 * (r ^ 3 * δ ^ 3) :=
        add_le_add (add_le_add hterm1 hterm2) hterm3
    _ ≤ Real.exp 3 * (r ^ 3 * δ ^ 3) +
          4 * Real.exp 3 * (r ^ 3 * δ ^ 3) +
            (9 / 2) * Real.exp 3 * (r ^ 3 * δ ^ 3) :=
        add_le_add (add_le_add hterm1' hterm2') (le_refl _)
    _ ≤ blocks3LocalConstant * blocks3LocalControl r := by
      unfold blocks3LocalConstant blocks3LocalControl
      dsimp [δ]
      have hnonneg : 0 ≤ r ^ 3 * (r ^ (-(7 / 6 : ℝ))) ^ 3 := by
        positivity
      nlinarith [Real.exp_pos 3, hnonneg]

lemma blocks3_local_uniform :
    ∀ ε > 0, ∀ᶠ (r : ℝ) in atTop, ∀ θ : ℝ,
      |θ| ≤ blocks3SaddleDeltaReal r →
        ‖saddleLocalRatio blocks3Fun blocks3SaddleAReal blocks3SaddleBReal r θ - 1‖ ≤ ε := by
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  have hsmall :
      ∀ᶠ r : ℝ in atTop, blocks3LocalConstant * blocks3LocalControl r ≤ ε / 2 :=
    blocks3LocalBound_tendsto_zero.eventually_le_const hhalf
  have hone :
      ∀ᶠ r : ℝ in atTop, blocks3LocalConstant * blocks3LocalControl r ≤ 1 :=
    blocks3LocalBound_tendsto_zero.eventually_le_const zero_lt_one
  filter_upwards [blocks3_local_exponent_norm_le_eventually, hsmall, hone] with
    r hloc hsmallr honer θ hθ
  rw [blocks3_saddleLocalRatio_eq]
  have hz : ‖blocks3LocalExponent r θ‖ ≤ blocks3LocalConstant * blocks3LocalControl r :=
    hloc θ hθ
  have hz_one : ‖blocks3LocalExponent r θ‖ ≤ 1 := hz.trans honer
  calc
    ‖Complex.exp (blocks3LocalExponent r θ) - 1‖
        ≤ 2 * ‖blocks3LocalExponent r θ‖ :=
          Complex.norm_exp_sub_one_le hz_one
    _ ≤ 2 * (blocks3LocalConstant * blocks3LocalControl r) :=
          mul_le_mul_of_nonneg_left hz (by norm_num)
    _ ≤ ε := by linarith

lemma blocks3_saddleGAt_norm (r : ℝ) (n : ℕ) (θ : ℝ) :
    ‖saddleGAt blocks3Fun r n θ‖ =
      Real.exp (r * (Real.cos θ - 1) +
        (r ^ 2 / 2) * (Real.cos (2 * θ) - 1) +
          (r ^ 3 / 6) * (Real.cos (3 * θ) - 1)) := by
  unfold saddleGAt blocks3Fun
  have hphase : ‖Complex.exp (-(↑↑n * ↑θ) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  have hden :
      ‖Complex.exp ((r : ℂ) + (r : ℂ) ^ 2 / 2 + (r : ℂ) ^ 3 / 6)‖ =
        Real.exp (r + r ^ 2 / 2 + r ^ 3 / 6) := by
    rw [Complex.norm_exp]
    congr 1
    rw [Complex.add_re, Complex.add_re]
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
    have hcube : (((r : ℂ) ^ 3 / 6).re = r ^ 3 / 6) := by
      rw [Complex.div_re]
      have hre : ((r : ℂ) ^ 3).re = r ^ 3 := by
        rw [pow_succ, pow_two, Complex.mul_re]
        simp
        ring
      have him : ((r : ℂ) ^ 3).im = 0 := by
        rw [pow_succ, pow_two, Complex.mul_im]
        simp
      rw [hre, him]
      norm_num [Complex.normSq]
      ring
    rw [hsq, hcube]
    simp
  have hnum_re :
      (((r : ℂ) * Complex.exp (θ * Complex.I)) +
          ((r : ℂ) * Complex.exp (θ * Complex.I)) ^ 2 / 2 +
            ((r : ℂ) * Complex.exp (θ * Complex.I)) ^ 3 / 6).re =
        r * Real.cos θ + (r ^ 2 / 2) * Real.cos (2 * θ) +
          (r ^ 3 / 6) * Real.cos (3 * θ) := by
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
    have hcube_div :
        ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ^ 3 / 6 =
          (((r ^ 3 / 6 : ℝ) : ℂ) * Complex.exp ((3 * θ : ℝ) * Complex.I)) := by
      have hcube0 :
          ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ^ 3 =
            ((r ^ 3 : ℝ) : ℂ) * Complex.exp ((3 * θ : ℝ) * Complex.I) := by
        rw [mul_pow, ← Complex.exp_nat_mul]
        rw [show (r : ℂ) ^ 3 = ((r ^ 3 : ℝ) : ℂ) by norm_num]
        rw [show (((3 : ℕ) : ℂ) * ((θ : ℂ) * Complex.I)) =
            ((3 * θ : ℝ) : ℂ) * Complex.I by
          simpa using complex_three_mul_theta_I θ]
      rw [hcube0]
      norm_num [Complex.ofReal_mul]
      ring_nf
    rw [hsq_div, hcube_div]
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
    have hre3 :
        ((((r ^ 3 / 6 : ℝ) : ℂ) * Complex.exp ((3 * θ : ℝ) * Complex.I)).re =
          (r ^ 3 / 6) * Real.cos (3 * θ)) := by
      rw [Complex.exp_ofReal_mul_I]
      simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero]
    rw [Complex.add_re, Complex.add_re, hre1, hre2, hre3]
  have hnum :
      ‖Complex.exp (((r : ℂ) * Complex.exp (↑θ * Complex.I)) +
          ((r : ℂ) * Complex.exp (↑θ * Complex.I)) ^ 2 / 2 +
            ((r : ℂ) * Complex.exp (↑θ * Complex.I)) ^ 3 / 6)‖ =
        Real.exp (r * Real.cos θ + (r ^ 2 / 2) * Real.cos (2 * θ) +
          (r ^ 3 / 6) * Real.cos (3 * θ)) := by
    rw [Complex.norm_exp, hnum_re]
  have hden_pos : 0 < Real.exp (r + r ^ 2 / 2 + r ^ 3 / 6) := Real.exp_pos _
  calc
    ‖Complex.exp (((r : ℂ) * Complex.exp (↑θ * Complex.I)) +
          ((r : ℂ) * Complex.exp (↑θ * Complex.I)) ^ 2 / 2 +
            ((r : ℂ) * Complex.exp (↑θ * Complex.I)) ^ 3 / 6) /
        Complex.exp ((r : ℂ) + (r : ℂ) ^ 2 / 2 + (r : ℂ) ^ 3 / 6) *
        Complex.exp (-(↑↑n * ↑θ) * Complex.I)‖
        = Real.exp (r * Real.cos θ + (r ^ 2 / 2) * Real.cos (2 * θ) +
              (r ^ 3 / 6) * Real.cos (3 * θ)) /
            Real.exp (r + r ^ 2 / 2 + r ^ 3 / 6) := by
          rw [norm_mul, hphase, mul_one, norm_div, hnum, hden]
    _ = Real.exp (r * (Real.cos θ - 1) +
          (r ^ 2 / 2) * (Real.cos (2 * θ) - 1) +
            (r ^ 3 / 6) * (Real.cos (3 * θ) - 1)) := by
      rw [← Real.exp_sub]
      congr 1
      ring_nf

def blocks3TailE (r : ℝ) : ℝ :=
  Real.exp (-(1 / (2 * Real.pi ^ 2)) * r ^ (2 / 3 : ℝ))

lemma blocks3TailE_nonneg_eventually :
    ∀ᶠ r : ℝ in atTop, 0 ≤ blocks3TailE r :=
  Eventually.of_forall fun r => by
    unfold blocks3TailE
    positivity

lemma blocks3TailE_decay :
    Tendsto (fun r : ℝ => Real.sqrt (2 * Real.pi * blocks3SaddleBReal r) * blocks3TailE r)
      atTop (𝓝 0) := by
  let c : ℝ := 1 / (2 * Real.pi ^ 2)
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hbase :
      Tendsto (fun y : ℝ => y ^ (9 / 4 : ℝ) * Real.exp (-c * y)) atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (9 / 4 : ℝ) c hc
  have hy : Tendsto (fun r : ℝ => r ^ (2 / 3 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)
  have hcomp :
      Tendsto (fun r : ℝ => (r ^ (2 / 3 : ℝ)) ^ (9 / 4 : ℝ) *
        Real.exp (-c * r ^ (2 / 3 : ℝ))) atTop (𝓝 0) :=
    hbase.comp hy
  have hscaled :
      Tendsto (fun r : ℝ => Real.sqrt (10 * Real.pi) *
        ((r ^ (2 / 3 : ℝ)) ^ (9 / 4 : ℝ) *
          Real.exp (-c * r ^ (2 / 3 : ℝ)))) atTop (𝓝 0) := by
    simpa using hcomp.const_mul (Real.sqrt (10 * Real.pi))
  refine squeeze_zero' ?_ ?_ hscaled
  · exact Eventually.of_forall fun r => by
      exact mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    have hr0 : 0 ≤ r := le_trans zero_le_one hr
    have one_le_r2 : 1 ≤ r ^ 2 := by nlinarith [hr, sq_nonneg (r - 1)]
    have hr_le_r3 : r ≤ r ^ 3 := by
      calc
        r = r * 1 := by ring
        _ ≤ r * r ^ 2 := mul_le_mul_of_nonneg_left one_le_r2 hr0
        _ = r ^ 3 := by ring
    have hr2_le_r3 : r ^ 2 ≤ r ^ 3 := by
      calc
        r ^ 2 = r ^ 2 * 1 := by ring
        _ ≤ r ^ 2 * r := mul_le_mul_of_nonneg_left hr (sq_nonneg r)
        _ = r ^ 3 := by ring
    have hB_le : blocks3SaddleBReal r ≤ 5 * r ^ 3 := by
      unfold blocks3SaddleBReal
      nlinarith
    have hsqrt :
        Real.sqrt (2 * Real.pi * blocks3SaddleBReal r) ≤
          Real.sqrt (10 * Real.pi) * r ^ (3 / 2 : ℝ) := by
      have hmul : 2 * Real.pi * blocks3SaddleBReal r ≤ 10 * Real.pi * r ^ 3 := by
        calc
          2 * Real.pi * blocks3SaddleBReal r
              ≤ 2 * Real.pi * (5 * r ^ 3) :=
                mul_le_mul_of_nonneg_left hB_le (by positivity)
          _ = 10 * Real.pi * r ^ 3 := by ring_nf
      calc
        Real.sqrt (2 * Real.pi * blocks3SaddleBReal r)
            ≤ Real.sqrt (10 * Real.pi * r ^ 3) := Real.sqrt_le_sqrt hmul
        _ = Real.sqrt (10 * Real.pi) * r ^ (3 / 2 : ℝ) := by
          have h10pi : 0 ≤ 10 * Real.pi := by positivity
          rw [Real.sqrt_mul h10pi (r ^ 3)]
          rw [Real.sqrt_eq_rpow (r ^ 3)]
          have hpow : (r ^ 3) ^ (1 / 2 : ℝ) = r ^ (3 / 2 : ℝ) := by
            rw [← Real.rpow_natCast]
            rw [← Real.rpow_mul hr0]
            norm_num
          rw [hpow]
    have hrpow : (r ^ (2 / 3 : ℝ)) ^ (9 / 4 : ℝ) = r ^ (3 / 2 : ℝ) := by
      rw [← Real.rpow_mul hr0]
      norm_num
    calc
      Real.sqrt (2 * Real.pi * blocks3SaddleBReal r) * blocks3TailE r
          ≤ (Real.sqrt (10 * Real.pi) * r ^ (3 / 2 : ℝ)) * blocks3TailE r :=
            mul_le_mul_of_nonneg_right hsqrt (by
              unfold blocks3TailE
              positivity)
      _ = Real.sqrt (10 * Real.pi) *
            ((r ^ (2 / 3 : ℝ)) ^ (9 / 4 : ℝ) *
              Real.exp (-c * r ^ (2 / 3 : ℝ))) := by
        unfold blocks3TailE
        dsimp [c]
        rw [hrpow]
        ring_nf

lemma blocks3_tail_bound_eventually :
    ∀ᶠ r : ℝ in atTop, ∀ n : ℕ, ∀ θ : ℝ,
      blocks3SaddleDeltaReal r ≤ |θ| → |θ| ≤ Real.pi →
        ‖saddleGAt blocks3Fun r n θ‖ ≤ blocks3TailE r := by
  let c : ℝ := 1 / (2 * Real.pi ^ 2)
  have hcpos : 0 < c := by
    dsimp [c]
    positivity
  have hc_le_three : c ≤ 3 / Real.pi ^ 2 := by
    dsimp [c]
    field_simp [Real.pi_ne_zero]
    norm_num
  have hc_le_two_ninths : c ≤ 2 / 9 := by
    dsimp [c]
    have hpi2 : (4 : ℝ) ≤ Real.pi ^ 2 := by
      nlinarith [Real.two_le_pi]
    have hden : 0 < 2 * Real.pi ^ 2 := by positivity
    rw [div_le_iff₀ hden]
    nlinarith
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr n θ hδθ hθπ
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  have hδ0 : 0 ≤ blocks3SaddleDeltaReal r := by
    unfold blocks3SaddleDeltaReal
    positivity
  rw [blocks3_saddleGAt_norm]
  unfold blocks3TailE
  apply Real.exp_le_exp.mpr
  by_cases hsmall : |θ| ≤ Real.pi / 3
  · have h3θπ : |3 * θ| ≤ Real.pi := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
      nlinarith
    have hcos3 := Real.cos_le_one_sub_mul_cos_sq h3θπ
    have hcos3_sub : Real.cos (3 * θ) - 1 ≤
        -(2 / Real.pi ^ 2) * (3 * θ) ^ 2 := by
      linarith
    have htail_scale :
        r ^ 3 * (blocks3SaddleDeltaReal r) ^ 2 = r ^ (2 / 3 : ℝ) := by
      have hr3_rpow : r ^ 3 = r ^ (3 : ℝ) := by
        exact (Real.rpow_natCast r 3).symm
      have hdelta_pow :
          (r ^ (-(7 / 6 : ℝ))) ^ 2 = r ^ (-(7 / 6 : ℝ) * (2 : ℝ)) :=
        (Real.rpow_mul_natCast hr0 (-(7 / 6 : ℝ)) 2).symm
      unfold blocks3SaddleDeltaReal
      calc
        r ^ 3 * (r ^ (-(7 / 6 : ℝ))) ^ 2
            = r ^ (3 : ℝ) * r ^ (-(7 / 6 : ℝ) * (2 : ℝ)) := by
              rw [hr3_rpow, hdelta_pow]
        _ = r ^ ((3 : ℝ) + (-(7 / 6 : ℝ) * (2 : ℝ))) := by
              rw [Real.rpow_add (lt_of_lt_of_le zero_lt_one hr)]
        _ = r ^ (2 / 3 : ℝ) := by norm_num
    have hθsq : (blocks3SaddleDeltaReal r) ^ 2 ≤ θ ^ 2 := by
      calc
        (blocks3SaddleDeltaReal r) ^ 2 ≤ |θ| ^ 2 :=
          pow_le_pow_left₀ hδ0 hδθ 2
        _ = θ ^ 2 := by rw [sq_abs]
    have hmain :
        r * (Real.cos θ - 1) +
          (r ^ 2 / 2) * (Real.cos (2 * θ) - 1) +
            (r ^ 3 / 6) * (Real.cos (3 * θ) - 1)
          ≤ -c * r ^ (2 / 3 : ℝ) := by
      have hcos1_nonpos : Real.cos θ - 1 ≤ 0 := by
        linarith [Real.cos_le_one θ]
      have hcos2_nonpos : Real.cos (2 * θ) - 1 ≤ 0 := by
        linarith [Real.cos_le_one (2 * θ)]
      have hleft_nonpos : r * (Real.cos θ - 1) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hr0 hcos1_nonpos
      have hmiddle_nonpos : (r ^ 2 / 2) * (Real.cos (2 * θ) - 1) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hcos2_nonpos
      have hcoef_nonpos : -(3 / Real.pi ^ 2) ≤ 0 := by
        have hpos : 0 ≤ 3 / Real.pi ^ 2 := by positivity
        linarith
      have hstrong :
          (r ^ 3 / 6) * (Real.cos (3 * θ) - 1)
            ≤ -(3 / Real.pi ^ 2) * (r ^ 3 * (blocks3SaddleDeltaReal r) ^ 2) := by
        calc
          (r ^ 3 / 6) * (Real.cos (3 * θ) - 1)
              ≤ (r ^ 3 / 6) * (-(2 / Real.pi ^ 2) * (3 * θ) ^ 2) :=
                mul_le_mul_of_nonneg_left hcos3_sub (by positivity)
          _ = -(3 / Real.pi ^ 2) * (r ^ 3 * θ ^ 2) := by ring_nf
          _ ≤ -(3 / Real.pi ^ 2) *
                (r ^ 3 * (blocks3SaddleDeltaReal r) ^ 2) := by
            exact mul_le_mul_of_nonpos_left
              (mul_le_mul_of_nonneg_left hθsq (by positivity)) hcoef_nonpos
      have hconst : c * r ^ (2 / 3 : ℝ) ≤
          (3 / Real.pi ^ 2) * (r ^ 3 * (blocks3SaddleDeltaReal r) ^ 2) := by
        rw [htail_scale]
        exact mul_le_mul_of_nonneg_right hc_le_three (Real.rpow_nonneg hr0 _)
      calc
        r * (Real.cos θ - 1) +
          (r ^ 2 / 2) * (Real.cos (2 * θ) - 1) +
            (r ^ 3 / 6) * (Real.cos (3 * θ) - 1)
            ≤ 0 + 0 +
                (-(3 / Real.pi ^ 2) *
                  (r ^ 3 * (blocks3SaddleDeltaReal r) ^ 2)) :=
              add_le_add (add_le_add hleft_nonpos hmiddle_nonpos) hstrong
        _ ≤ -c * r ^ (2 / 3 : ℝ) := by linarith
    exact hmain
  · have hlarge : Real.pi / 3 < |θ| := lt_of_not_ge hsmall
    have hcos1 := Real.cos_le_one_sub_mul_cos_sq hθπ
    have hcos1_sub : Real.cos θ - 1 ≤ -(2 / Real.pi ^ 2) * θ ^ 2 := by
      linarith
    have hθsq_lower : (Real.pi / 3) ^ 2 ≤ θ ^ 2 := by
      calc
        (Real.pi / 3) ^ 2 ≤ |θ| ^ 2 :=
          pow_le_pow_left₀ (by positivity) hlarge.le 2
        _ = θ ^ 2 := by rw [sq_abs]
    have hmain :
        r * (Real.cos θ - 1) +
          (r ^ 2 / 2) * (Real.cos (2 * θ) - 1) +
            (r ^ 3 / 6) * (Real.cos (3 * θ) - 1)
          ≤ -c * r ^ (2 / 3 : ℝ) := by
      have hcos2_nonpos : Real.cos (2 * θ) - 1 ≤ 0 := by
        linarith [Real.cos_le_one (2 * θ)]
      have hcos3_nonpos : Real.cos (3 * θ) - 1 ≤ 0 := by
        linarith [Real.cos_le_one (3 * θ)]
      have hmiddle_nonpos : (r ^ 2 / 2) * (Real.cos (2 * θ) - 1) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hcos2_nonpos
      have hright_nonpos : (r ^ 3 / 6) * (Real.cos (3 * θ) - 1) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hcos3_nonpos
      have hcoef_nonpos : -(2 / Real.pi ^ 2) ≤ 0 := by
        have hpos : 0 ≤ 2 / Real.pi ^ 2 := by positivity
        linarith
      have hfirst :
          r * (Real.cos θ - 1) ≤ -(2 / 9) * r := by
        calc
          r * (Real.cos θ - 1)
              ≤ r * (-(2 / Real.pi ^ 2) * θ ^ 2) :=
                mul_le_mul_of_nonneg_left hcos1_sub hr0
          _ ≤ r * (-(2 / Real.pi ^ 2) * (Real.pi / 3) ^ 2) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonpos_left hθsq_lower hcoef_nonpos) hr0
          _ = -(2 / 9) * r := by
            field_simp [Real.pi_ne_zero]
            ring
      have hpow_le : r ^ (2 / 3 : ℝ) ≤ r := by
        calc
          r ^ (2 / 3 : ℝ) ≤ r ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hr (by norm_num : (2 / 3 : ℝ) ≤ 1)
          _ = r := by rw [Real.rpow_one]
      have hconst : c * r ^ (2 / 3 : ℝ) ≤ (2 / 9) * r := by
        calc
          c * r ^ (2 / 3 : ℝ) ≤ (2 / 9) * r ^ (2 / 3 : ℝ) :=
            mul_le_mul_of_nonneg_right hc_le_two_ninths (Real.rpow_nonneg hr0 _)
          _ ≤ (2 / 9) * r :=
            mul_le_mul_of_nonneg_left hpow_le (by norm_num)
      calc
        r * (Real.cos θ - 1) +
          (r ^ 2 / 2) * (Real.cos (2 * θ) - 1) +
            (r ^ 3 / 6) * (Real.cos (3 * θ) - 1)
            ≤ -(2 / 9) * r + 0 + 0 :=
              add_le_add (add_le_add hfirst hmiddle_nonpos) hright_nonpos
        _ ≤ -c * r ^ (2 / 3 : ℝ) := by linarith
    exact hmain

lemma blocks3_tail_uniform :
    ∃ E : ℝ → ℝ,
      (∀ᶠ (r : ℝ) in atTop, 0 ≤ E r) ∧
      Tendsto (fun r : ℝ => Real.sqrt (2 * Real.pi * blocks3SaddleBReal r) * E r)
        atTop (𝓝 0) ∧
      (∀ᶠ (r : ℝ) in atTop, ∀ n : ℕ, ∀ θ : ℝ,
        blocks3SaddleDeltaReal r ≤ |θ| → |θ| ≤ Real.pi →
          ‖saddleGAt blocks3Fun r n θ‖ ≤ E r) := by
  exact ⟨blocks3TailE, blocks3TailE_nonneg_eventually, blocks3TailE_decay,
    blocks3_tail_bound_eventually⟩

lemma blocks3SaddleAReal_strictMonoOn_nonneg :
    StrictMonoOn blocks3SaddleAReal (Set.Ici (0 : ℝ)) := by
  intro x hx y hy hxy
  unfold blocks3SaddleAReal
  have hdiff : 0 < y - x := sub_pos.mpr hxy
  have hx0 : 0 ≤ x := hx
  have hy0 : 0 ≤ y := hy
  have hxy0 : 0 ≤ x * y := mul_nonneg hx0 hy0
  have hquad_nonneg : 0 ≤ (x ^ 2 + x * y + y ^ 2) / 2 := by
    nlinarith [sq_nonneg x, sq_nonneg y, hxy0]
  have hfactor : 0 < 1 + x + y + (x ^ 2 + x * y + y ^ 2) / 2 := by
    linarith
  have hpos : 0 < (y - x) *
      (1 + x + y + (x ^ 2 + x * y + y ^ 2) / 2) :=
    mul_pos hdiff hfactor
  nlinarith

lemma blocks3SaddleAReal_exists_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    ∃ r : ℝ, 0 ≤ r ∧ blocks3SaddleAReal r = x := by
  rcases eq_or_lt_of_le hx with rfl | hxpos
  · refine ⟨0, by norm_num, ?_⟩
    simp [blocks3SaddleAReal]
  · have hcont : ContinuousOn blocks3SaddleAReal (Set.Icc (0 : ℝ) x) := by
      unfold blocks3SaddleAReal
      fun_prop
    have hleft : blocks3SaddleAReal 0 ≤ x := by
      simp [blocks3SaddleAReal, hx]
    have hright : x ≤ blocks3SaddleAReal x := by
      unfold blocks3SaddleAReal
      have hx0 : 0 ≤ x := hxpos.le
      nlinarith [sq_nonneg x, mul_nonneg (sq_nonneg x) hx0]
    have hxI : x ∈ Set.Icc (blocks3SaddleAReal 0) (blocks3SaddleAReal x) :=
      ⟨hleft, hright⟩
    rcases intermediate_value_Icc hxpos.le hcont hxI with ⟨r, hrmem, hr⟩
    exact ⟨r, hrmem.1, hr⟩

/-- The nonnegative saddle radius solving `r+r^2+r^3/2=n`. -/
noncomputable def blocks3SaddleRadius (n : ℕ) : ℝ :=
  Classical.choose (blocks3SaddleAReal_exists_of_nonneg
    (Nat.cast_nonneg n : 0 ≤ (n : ℝ)))

lemma blocks3SaddleRadius_nonneg (n : ℕ) : 0 ≤ blocks3SaddleRadius n :=
  (Classical.choose_spec
    (blocks3SaddleAReal_exists_of_nonneg (Nat.cast_nonneg n : 0 ≤ (n : ℝ)))).1

lemma blocks3SaddleAReal_radius (n : ℕ) :
    blocks3SaddleAReal (blocks3SaddleRadius n) = (n : ℝ) :=
  (Classical.choose_spec
    (blocks3SaddleAReal_exists_of_nonneg (Nat.cast_nonneg n : 0 ≤ (n : ℝ)))).2

lemma blocks3SaddleRadius_tendsto_atTop :
    Tendsto blocks3SaddleRadius atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro M
  let M0 : ℝ := max M 0
  obtain ⟨N, hN⟩ := exists_nat_gt (blocks3SaddleAReal M0)
  refine ⟨N, fun n hn => ?_⟩
  have hM0_nonneg : 0 ≤ M0 := le_max_right _ _
  have hM_le_M0 : M ≤ M0 := le_max_left _ _
  have hnR : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hAM0_lt_n : blocks3SaddleAReal M0 < (n : ℝ) := hN.trans_le hnR
  by_contra hnot
  have hr_lt_M : blocks3SaddleRadius n < M := lt_of_not_ge hnot
  have hr_lt_M0 : blocks3SaddleRadius n < M0 := hr_lt_M.trans_le hM_le_M0
  have hstrict :
      blocks3SaddleAReal (blocks3SaddleRadius n) < blocks3SaddleAReal M0 :=
    blocks3SaddleAReal_strictMonoOn_nonneg
      (blocks3SaddleRadius_nonneg n) hM0_nonneg hr_lt_M0
  rw [blocks3SaddleAReal_radius] at hstrict
  linarith

def blocks3HAdmissible : HAdmissible blocks3Fun blocks3Series where
  ρ := blocks3Series.radius
  radFilter := atTop
  a := blocks3SaddleAReal
  b := blocks3SaddleBReal
  δ := blocks3SaddleDeltaReal
  hp := blocks3Fun_hasFPowerSeriesAt_zero
  radius_eq := rfl
  radius_pos := by
    simpa [blocks3Series] using blocks3Fun_hasFPowerSeriesAt_zero.radius_pos
  rad_neBot := by infer_instance
  r_pos := eventually_gt_atTop (0 : ℝ)
  differentiableOn := blocks3_differentiableOn_eventually
  f_pos := blocks3_f_pos_eventually
  b_pos := blocks3_b_pos_eventually
  δ_pos := blocks3_delta_pos_eventually
  δ_le_pi := blocks3_delta_le_pi_eventually
  δ_sqrt_b_tendsto_atTop := blocks3_delta_sqrt_b_tendsto_atTop
  local_uniform := blocks3_local_uniform
  tail_uniform := blocks3_tail_uniform

def blocks3HAdmissibleSaddleSequence : SaddleSequence blocks3HAdmissible where
  r := blocks3SaddleRadius
  tendsTo := by
    simpa [blocks3HAdmissible] using blocks3SaddleRadius_tendsto_atTop
  saddle_eq := by
    exact Eventually.of_forall fun n => by
      change blocks3SaddleAReal (blocks3SaddleRadius n) = (n : ℝ)
      exact blocks3SaddleAReal_radius n

theorem blocks3_coeff_isEquivalent_saddle_from_HAdmissible :
    (fun n : ℕ => blocks3Series.coeff n) ~[atTop]
      (fun n : ℕ => saddleScale blocks3Fun blocks3SaddleRadius
        (fun n => blocks3SaddleBReal (blocks3SaddleRadius n)) n) := by
  have h := coeff_isEquivalent_saddle blocks3HAdmissible blocks3HAdmissibleSaddleSequence
  simpa [HAdmissible.B, blocks3HAdmissibleSaddleSequence, blocks3HAdmissible] using h

theorem blocks3_count_over_factorial_isEquivalent_saddle :
    (fun n : ℕ =>
      (((AnalyticCombinatorics.Ch1.CombClass.blocks3.counts n : ℝ) / n.factorial : ℝ) : ℂ))
      ~[atTop]
      (fun n : ℕ => saddleScale blocks3Fun blocks3SaddleRadius
        (fun n => blocks3SaddleBReal (blocks3SaddleRadius n)) n) := by
  simpa [blocks3Series, PowerSeries.coeff_toFMLS, blocks3Carrier_coeff, blocks3CoeffR] using
    blocks3_coeff_isEquivalent_saddle_from_HAdmissible

theorem blocks3_count_isEquivalent_factorial_mul_saddle :
    (fun n : ℕ =>
      ((AnalyticCombinatorics.Ch1.CombClass.blocks3.counts n : ℝ) : ℂ))
      ~[atTop]
      (fun n : ℕ => ((n.factorial : ℝ) : ℂ) *
        saddleScale blocks3Fun blocks3SaddleRadius
          (fun n => blocks3SaddleBReal (blocks3SaddleRadius n)) n) := by
  have hfact :
      (fun n : ℕ => ((n.factorial : ℝ) : ℂ)) ~[atTop]
        (fun n : ℕ => ((n.factorial : ℝ) : ℂ)) :=
    Asymptotics.IsEquivalent.refl
  have h := hfact.mul blocks3_count_over_factorial_isEquivalent_saddle
  refine h.congr_left ?_
  refine Eventually.of_forall fun n => ?_
  have hfact_ne : ((n.factorial : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_ne_zero n)
  change ((n.factorial : ℝ) : ℂ) *
      (((AnalyticCombinatorics.Ch1.CombClass.blocks3.counts n : ℝ) /
        n.factorial : ℝ) : ℂ) =
    ((AnalyticCombinatorics.Ch1.CombClass.blocks3.counts n : ℝ) : ℂ)
  norm_num [Complex.ofReal_div]
  field_simp [hfact_ne]
  exact mul_div_cancel_left₀
    (((AnalyticCombinatorics.Ch1.CombClass.blocks3.counts n : ℝ) : ℂ)) hfact_ne

end Blocks3HAdmissible
