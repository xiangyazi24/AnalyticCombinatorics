import AnalyticCombinatorics.Ch4.Analytic.SqrtSingularityThirdOrder
import AnalyticCombinatorics.Ch7.SingularityApp.RiordanSecondOrder

/-!
# Third-order Riordan asymptotics

This file plugs the Riordan square-root data at `ρ = 1 / 3` into the
third-order square-root applicator.
-/

set_option maxHeartbeats 1200000

open Complex Filter Asymptotics Set
open scoped Topology BigOperators PowerSeries

noncomputable section

def riordanRho : ℝ := 1 / 3

def riordanAnalyticQuadraticCoeff : ℂ := 3 / 2

def riordanSingularDerivAtRho : ℂ :=
  (((81 * Real.sqrt 3 / 32 : ℝ) : ℂ))

def riordanSingularSecondDerivAtRho : ℂ :=
  -(((3969 * Real.sqrt 3 / 256 : ℝ) : ℂ))

def riordanThirdSingularCoeff : ℂ :=
  -(((441 * Real.sqrt 3 / 512 : ℝ) : ℂ))

def riordanThirdAsymptoticConstant : ℝ :=
  2055 * Real.sqrt 3 / (4096 * Real.sqrt Real.pi)

def riordanRelativeThirdConstant : ℝ := 685 / 512

def riordanOneSubThreeXSeriesℂ : PowerSeries ℂ :=
  (1 : PowerSeries ℂ) - PowerSeries.C (3 : ℂ) * PowerSeries.X

def riordanThirdOriginalSeriesℂ : PowerSeries ℂ :=
  riordanSeriesℂ -
    PowerSeries.C riordanAnalyticQuadraticCoeff * riordanOneSubThreeXSeriesℂ ^ 2

def riordanThirdAdjustedRescaledSeriesℂ : PowerSeries ℂ :=
  riordanRescaledSeriesℂ -
    PowerSeries.C riordanAnalyticQuadraticCoeff * riordanOneSubSeriesℂ ^ 2

def riordanOriginalFun (z : ℂ) : ℂ :=
  riordanRescaledFun (3 * z)

def riordanThirdOriginalFun (z : ℂ) : ℂ :=
  riordanOriginalFun z - riordanAnalyticQuadraticCoeff * (1 - 3 * z) ^ 2

def riordanThirdAdjustedRescaledFun (z : ℂ) : ℂ :=
  riordanRescaledFun z - riordanAnalyticQuadraticCoeff * (1 - z) ^ 2

lemma riordanThirdOriginalFun_rescale (z : ℂ) :
    riordanThirdOriginalFun (((riordanRho : ℝ) : ℂ) * z) =
      riordanThirdAdjustedRescaledFun z := by
  unfold riordanThirdOriginalFun riordanOriginalFun riordanThirdAdjustedRescaledFun
    riordanRho riordanAnalyticQuadraticCoeff
  have hscale : 3 * (((1 / 3 : ℝ) : ℂ) * z) = z := by
    have h : (3 : ℂ) * (((1 / 3 : ℝ) : ℂ)) = 1 := by norm_num
    calc
      3 * (((1 / 3 : ℝ) : ℂ) * z) =
          ((3 : ℂ) * (((1 / 3 : ℝ) : ℂ))) * z := by ring
      _ = z := by rw [h]; ring
  rw [hscale]

private lemma PowerSeries_rescale_C (a c : ℂ) :
    PowerSeries.rescale a (PowerSeries.C c) = PowerSeries.C c := by
  ext n
  rw [PowerSeries.coeff_rescale]
  cases n with
  | zero =>
      simp
  | succ n =>
      simp

lemma rescale_riordanOneSubThreeXSeriesℂ :
    PowerSeries.rescale (((riordanRho : ℝ) : ℂ)) riordanOneSubThreeXSeriesℂ =
      riordanOneSubSeriesℂ := by
  ext n
  rw [PowerSeries.coeff_rescale]
  cases n with
  | zero =>
      simp [riordanOneSubThreeXSeriesℂ, riordanOneSubSeriesℂ]
  | succ n =>
      cases n with
      | zero =>
          simp [riordanOneSubThreeXSeriesℂ, riordanOneSubSeriesℂ, riordanRho,
            PowerSeries.coeff_X, PowerSeries.coeff_C]
      | succ n =>
          simp [riordanOneSubThreeXSeriesℂ, riordanOneSubSeriesℂ, PowerSeries.coeff_X]

lemma rescale_riordanThirdOriginalSeriesℂ :
    PowerSeries.rescale (((riordanRho : ℝ) : ℂ)) riordanThirdOriginalSeriesℂ =
      riordanThirdAdjustedRescaledSeriesℂ := by
  unfold riordanThirdOriginalSeriesℂ riordanThirdAdjustedRescaledSeriesℂ
  simp only [map_sub, map_mul, map_pow,
    rescale_riordanOneSubThreeXSeriesℂ]
  rw [PowerSeries_rescale_C]
  have hρ : (((riordanRho : ℝ) : ℂ)) = (3 : ℂ)⁻¹ := by
    unfold riordanRho
    norm_num
  rw [hρ]
  rfl

lemma riordanThirdAdjustedRescaledFun_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt riordanThirdAdjustedRescaledFun
      (PowerSeries.toFMLS riordanThirdAdjustedRescaledSeriesℂ) (0 : ℂ) := by
  have hsquare : HasFPowerSeriesAt (fun z : ℂ => (1 - z) * (1 - z))
      (PowerSeries.toFMLS (riordanOneSubSeriesℂ ^ 2)) (0 : ℂ) := by
    simpa [pow_two] using
      hasFPowerSeriesAt_mul_toFMLS hasFPowerSeriesAt_riordanOneSub_toFMLS
        hasFPowerSeriesAt_riordanOneSub_toFMLS
  have hquad : HasFPowerSeriesAt
      (fun z : ℂ => riordanAnalyticQuadraticCoeff * (1 - z) ^ 2)
      (PowerSeries.toFMLS
        (PowerSeries.C riordanAnalyticQuadraticCoeff * riordanOneSubSeriesℂ ^ 2))
      (0 : ℂ) := by
    have h := hsquare.const_smul (c := riordanAnalyticQuadraticCoeff)
    convert h using 1
    · ext z
      simp [pow_two, smul_eq_mul]
    · ext n
      simp [PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars,
        PowerSeries.coeff_C_mul]
  have hsub := riordanRescaledFun_hasFPowerSeriesAt_zero.sub hquad
  simpa [riordanThirdAdjustedRescaledFun, riordanThirdAdjustedRescaledSeriesℂ,
    toFMLS_sub] using hsub

lemma riordanThirdOriginalFun_rescaled_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt
      (fun z : ℂ => riordanThirdOriginalFun (((riordanRho : ℝ) : ℂ) * z))
      (PowerSeries.toFMLS
        (PowerSeries.rescale (((riordanRho : ℝ) : ℂ)) riordanThirdOriginalSeriesℂ))
      (0 : ℂ) := by
  rw [rescale_riordanThirdOriginalSeriesℂ]
  simpa [riordanThirdOriginalFun_rescale] using
    riordanThirdAdjustedRescaledFun_hasFPowerSeriesAt_zero

lemma analyticOnNhd_riordanThirdAdjustedRescaledFun :
    AnalyticOnNhd ℂ riordanThirdAdjustedRescaledFun
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
  have hquad : AnalyticOnNhd ℂ
      (fun z : ℂ => riordanAnalyticQuadraticCoeff * (1 - z) ^ 2)
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
    simpa [pow_two] using
      (analyticOnNhd_const.mul
        ((analyticOnNhd_const.sub analyticOnNhd_id).mul
          (analyticOnNhd_const.sub analyticOnNhd_id)))
  simpa [riordanThirdAdjustedRescaledFun] using
    analyticOnNhd_riordanRescaledFun.sub hquad

lemma analyticOnNhd_riordanThirdOriginalFun_rescaled :
    AnalyticOnNhd ℂ
      (fun z : ℂ => riordanThirdOriginalFun (((riordanRho : ℝ) : ℂ) * z))
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
  simpa [riordanThirdOriginalFun_rescale] using
    analyticOnNhd_riordanThirdAdjustedRescaledFun

def riordanAnalyticPart (z : ℂ) : ℂ :=
  (3 / 2 : ℂ) / z

def riordanSingularPart (z : ℂ) : ℂ :=
  -(3 / 2 : ℂ) / (z * riordanSqrtPlus z)

def riordanOneSubInvTaylor (u : ℂ) : ℂ :=
  1 + u + u ^ 2

def riordanSqrtPlusInvTaylor (u : ℂ) : ℂ :=
  (((Real.sqrt 3 / 2 : ℝ) : ℂ)) * (1 + u / 8 + 3 * u ^ 2 / 128)

def riordanSingularPartTaylorFull (u : ℂ) : ℂ :=
  -(3 / 2 : ℂ) * riordanOneSubInvTaylor u * riordanSqrtPlusInvTaylor u

private lemma tendsto_isBigO_one_complex {α : Type*} [TopologicalSpace α]
    {l : Filter α} {f : α → ℂ} {a : ℂ} (hf : Tendsto f l (𝓝 a)) :
    f =O[l] (fun _ : α => (1 : ℝ)) := by
  refine IsBigO.of_bound (‖a‖ + 1) ?_
  have hlt : ‖a‖ < ‖a‖ + 1 := by linarith
  filter_upwards [hf.norm.eventually (Iio_mem_nhds hlt)] with x hx
  simpa using le_of_lt hx

private lemma cubic_mul_continuous_isBigO (g : ℂ → ℂ)
    (hg : ContinuousAt g 0) :
    (fun u : ℂ => u ^ 3 * g u) =O[𝓝 (0 : ℂ)]
      (fun u : ℂ => ‖u‖ ^ 3) := by
  refine IsBigO.of_bound (‖g 0‖ + 1) ?_
  have hlt : ‖g 0‖ < ‖g 0‖ + 1 := by linarith
  filter_upwards [hg.norm.eventually (Iio_mem_nhds hlt)] with u hu
  rw [norm_mul, norm_pow]
  have hnonneg : 0 ≤ ‖u‖ ^ 3 := by positivity
  calc
    ‖u‖ ^ 3 * ‖g u‖ ≤ ‖u‖ ^ 3 * (‖g 0‖ + 1) :=
      mul_le_mul_of_nonneg_left (le_of_lt hu) hnonneg
    _ = (‖g 0‖ + 1) * ‖‖u‖ ^ 3‖ := by
      rw [Real.norm_of_nonneg hnonneg]
      ring

private lemma norm_rpow_half_tendsto_zero :
    Tendsto (fun u : ℂ => ‖u‖ ^ (1 / 2 : ℝ)) (𝓝 (0 : ℂ)) (𝓝 0) := by
  have hpow : ContinuousAt (fun x : ℝ => x ^ (1 / 2 : ℝ)) 0 :=
    Real.continuousAt_rpow_const 0 (1 / 2 : ℝ)
      (Or.inr (by norm_num : (0 : ℝ) ≤ 1 / 2))
  have h := hpow.tendsto.comp
    (tendsto_norm_zero : Tendsto (fun u : ℂ => ‖u‖) (𝓝 0) (𝓝 0))
  change Tendsto (fun u : ℂ => ‖u‖ ^ (1 / 2 : ℝ)) (𝓝 0)
    (𝓝 ((0 : ℝ) ^ (1 / 2 : ℝ))) at h
  norm_num at h
  exact h

private lemma norm_pow_three_isLittleO_norm_rpow_five_halves :
    (fun u : ℂ => ‖u‖ ^ 3) =o[𝓝 (0 : ℂ)]
      (fun u : ℂ => ‖u‖ ^ (5 / 2 : ℝ)) := by
  have hsmall : (fun u : ℂ => ‖u‖ ^ (1 / 2 : ℝ)) =o[𝓝 (0 : ℂ)]
      (fun _ : ℂ => (1 : ℝ)) :=
    (isLittleO_one_iff ℝ).2 norm_rpow_half_tendsto_zero
  have hbase : (fun u : ℂ => ‖u‖ ^ (5 / 2 : ℝ)) =O[𝓝 (0 : ℂ)]
      (fun u : ℂ => ‖u‖ ^ (5 / 2 : ℝ)) := isBigO_refl _ _
  have hprod := hbase.mul_isLittleO hsmall
  refine hprod.congr' ?_ ?_
  · filter_upwards with u
    by_cases hu : u = 0
    · simp [hu]
    · have hpos : 0 < ‖u‖ := norm_pos_iff.mpr hu
      rw [← Real.rpow_add hpos]
      norm_num
  · filter_upwards with u
    ring

private lemma norm_pow_three_mul_rpow_half_isLittleO_norm_rpow_five_halves :
    (fun u : ℂ => ‖u‖ ^ 3 * ‖u‖ ^ (1 / 2 : ℝ)) =o[𝓝 (0 : ℂ)]
      (fun u : ℂ => ‖u‖ ^ (5 / 2 : ℝ)) := by
  have hsmall : (fun u : ℂ => ‖u‖) =o[𝓝 (0 : ℂ)]
      (fun _ : ℂ => (1 : ℝ)) :=
    (isLittleO_one_iff ℝ).2 tendsto_norm_zero
  have hbase : (fun u : ℂ => ‖u‖ ^ (5 / 2 : ℝ)) =O[𝓝 (0 : ℂ)]
      (fun u : ℂ => ‖u‖ ^ (5 / 2 : ℝ)) := isBigO_refl _ _
  have hprod := hbase.mul_isLittleO hsmall
  refine hprod.congr' ?_ ?_
  · filter_upwards with u
    by_cases hu : u = 0
    · simp [hu]
    · have hpos : 0 < ‖u‖ := norm_pos_iff.mpr hu
      calc
        ‖u‖ ^ (5 / 2 : ℝ) * ‖u‖ =
            ‖u‖ ^ (5 / 2 : ℝ) * ‖u‖ ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = ‖u‖ ^ ((5 / 2 : ℝ) + 1) := by rw [← Real.rpow_add hpos]
        _ = ‖u‖ ^ (3 + (1 / 2 : ℝ)) := by norm_num
        _ = ‖u‖ ^ 3 * ‖u‖ ^ (1 / 2 : ℝ) := by
          rw [Real.rpow_add hpos]
          norm_num
  · filter_upwards with u
    ring

lemma riordanSqrtPlus_ne_zero_of_norm_lt_three {z : ℂ} (hz : ‖z‖ < 3) :
    riordanSqrtPlus z ≠ 0 := by
  intro h
  have hsq := riordanSqrtPlus_sq z
  rw [h] at hsq
  norm_num at hsq
  have hsum : 1 + z / 3 = 0 := by simpa using hsq.symm
  have hz_eq : z = -3 := by linear_combination 3 * hsum
  have hnorm : ‖z‖ = 3 := by rw [hz_eq]; norm_num
  nlinarith

lemma riordanRescaledFun_decomp {z : ℂ} (hz0 : z ≠ 0) (hznorm : ‖z‖ < 3) :
    riordanRescaledFun z =
      riordanAnalyticPart z + riordanSingularPart z * riordanSqrtOneSub z := by
  have hD : riordanRescaledDenominator z ≠ 0 :=
    riordanRescaledDenominator_ne_zero_of_norm_lt_three hznorm
  have ht : riordanSqrtPlus z ≠ 0 := riordanSqrtPlus_ne_zero_of_norm_lt_three hznorm
  unfold riordanRescaledFun riordanAnalyticPart riordanSingularPart
  field_simp [hD, hz0, ht]
  unfold riordanRescaledDenominator
  ring_nf
  rw [riordanSqrtPlus_sq, riordanSqrtOneSub_sq]
  ring

lemma riordanAnalyticPart_remainder_isBigO :
    (fun u : ℂ =>
      riordanAnalyticPart (1 - u) -
        (riordanRegularValueℂ + riordanAnalyticLinearCoeff * u +
          riordanAnalyticQuadraticCoeff * u ^ 2))
      =O[𝓝 (0 : ℂ)] (fun u : ℂ => ‖u‖ ^ 3) := by
  have hbase := cubic_mul_continuous_isBigO
    (fun u : ℂ => (3 / 2 : ℂ) / (1 - u))
    (by
      apply ContinuousAt.div
      · fun_prop
      · fun_prop
      · norm_num)
  refine hbase.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_ne_nhds (show (0 : ℂ) ≠ 1 by norm_num)] with u hu
  unfold riordanAnalyticPart riordanRegularValueℂ riordanAnalyticLinearCoeff
    riordanAnalyticQuadraticCoeff
  field_simp [sub_ne_zero.mpr (Ne.symm hu)]
  ring

lemma riordanOneSubInv_sub_taylor_isBigO :
    (fun u : ℂ => (1 - u)⁻¹ - riordanOneSubInvTaylor u)
      =O[𝓝 (0 : ℂ)] (fun u : ℂ => ‖u‖ ^ 3) := by
  have hbase := cubic_mul_continuous_isBigO
    (fun u : ℂ => (1 - u)⁻¹)
    (by
      apply ContinuousAt.inv₀
      · fun_prop
      · norm_num)
  refine hbase.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_ne_nhds (show (0 : ℂ) ≠ 1 by norm_num)] with u hu
  unfold riordanOneSubInvTaylor
  field_simp [sub_ne_zero.mpr (Ne.symm hu)]
  ring

lemma riordanSqrtPlusInvTaylor_sq_residual (u : ℂ) :
    1 - (riordanSqrtPlus (1 - u) * riordanSqrtPlusInvTaylor u) ^ 2 =
      u ^ 3 * ((5 / 512 : ℂ) + (15 / 16384 : ℂ) * u + (9 / 65536 : ℂ) * u ^ 2) := by
  rw [show (riordanSqrtPlus (1 - u) * riordanSqrtPlusInvTaylor u) ^ 2 =
      (riordanSqrtPlus (1 - u)) ^ 2 * (riordanSqrtPlusInvTaylor u) ^ 2 by ring]
  rw [riordanSqrtPlus_sq]
  unfold riordanSqrtPlusInvTaylor
  norm_num [Complex.ofReal_div, Complex.ofReal_mul]
  ring_nf
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num
  ring_nf

lemma riordanSqrtPlusInvTaylor_sq_residual_isBigO :
    (fun u : ℂ => 1 - (riordanSqrtPlus (1 - u) * riordanSqrtPlusInvTaylor u) ^ 2)
      =O[𝓝 (0 : ℂ)] (fun u : ℂ => ‖u‖ ^ 3) := by
  have hbase := cubic_mul_continuous_isBigO
    (fun u : ℂ => (5 / 512 : ℂ) + (15 / 16384 : ℂ) * u + (9 / 65536 : ℂ) * u ^ 2)
    (by fun_prop)
  refine hbase.congr_left ?_
  intro u
  rw [riordanSqrtPlusInvTaylor_sq_residual]

lemma riordanSqrtPlusInv_sub_taylor_isBigO :
    (fun u : ℂ => (riordanSqrtPlus (1 - u))⁻¹ - riordanSqrtPlusInvTaylor u)
      =O[𝓝 (0 : ℂ)] (fun u : ℂ => ‖u‖ ^ 3) := by
  let t : ℂ → ℂ := fun u => riordanSqrtPlus (1 - u)
  let q : ℂ → ℂ := riordanSqrtPlusInvTaylor
  have ht : Tendsto t (𝓝 (0 : ℂ)) (𝓝 riordanSqrtPlusAtOneℂ) := by
    have harg : Tendsto (fun u : ℂ => 1 - u) (𝓝 (0 : ℂ)) (𝓝 (1 : ℂ)) := by
      simpa using
        (continuousAt_const.sub continuousAt_id :
          ContinuousAt (fun u : ℂ => 1 - u) 0).tendsto
    simpa [t, riordanSqrtPlus_one] using
      hasDerivAt_riordanSqrtPlus_one.continuousAt.tendsto.comp harg
  have hq : Tendsto q (𝓝 (0 : ℂ)) (𝓝 ((((Real.sqrt 3 / 2 : ℝ) : ℂ)))) := by
    have hcont : ContinuousAt q 0 := by
      unfold q riordanSqrtPlusInvTaylor
      fun_prop
    simpa [q, riordanSqrtPlusInvTaylor] using hcont.tendsto
  have htq : Tendsto (fun u : ℂ => t u * q u) (𝓝 (0 : ℂ)) (𝓝 (1 : ℂ)) := by
    have hmul := ht.mul hq
    convert hmul using 1
    unfold riordanSqrtPlusAtOneℂ
    have hs3 : ((Real.sqrt 3 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 3))
    norm_num [Complex.ofReal_div, Complex.ofReal_mul]
  have hsum_tendsto : Tendsto (fun u : ℂ => 1 + t u * q u)
      (𝓝 (0 : ℂ)) (𝓝 (2 : ℂ)) := by
    convert tendsto_const_nhds.add htq using 1
    norm_num
  have hden : Tendsto (fun u : ℂ => (1 + t u * q u)⁻¹)
      (𝓝 (0 : ℂ)) (𝓝 ((2 : ℂ)⁻¹)) :=
    hsum_tendsto.inv₀ (by norm_num : (2 : ℂ) ≠ 0)
  have hdenO : (fun u : ℂ => (1 + t u * q u)⁻¹)
      =O[𝓝 (0 : ℂ)] (fun _ : ℂ => (1 : ℝ)) :=
    tendsto_isBigO_one_complex hden
  have hprod := riordanSqrtPlusInvTaylor_sq_residual_isBigO.mul hdenO
  have hone_minus : (fun u : ℂ => 1 - t u * q u)
      =O[𝓝 (0 : ℂ)] (fun u : ℂ => ‖u‖ ^ 3) := by
    refine hprod.congr' ?_ ?_
    · have hsum_ne : ∀ᶠ u : ℂ in 𝓝 (0 : ℂ), 1 + t u * q u ≠ 0 :=
        hsum_tendsto.eventually_ne (by norm_num : (2 : ℂ) ≠ 0)
      filter_upwards [hsum_ne] with u hu
      dsimp [t, q] at hu ⊢
      rw [show 1 - riordanSqrtPlus (1 - u) * riordanSqrtPlusInvTaylor u =
          (1 - (riordanSqrtPlus (1 - u) * riordanSqrtPlusInvTaylor u) ^ 2) *
            (1 + riordanSqrtPlus (1 - u) * riordanSqrtPlusInvTaylor u)⁻¹ by
        field_simp [hu]
        ring]
    · filter_upwards with u
      ring
  have htinv : Tendsto (fun u : ℂ => (t u)⁻¹)
      (𝓝 (0 : ℂ)) (𝓝 (riordanSqrtPlusAtOneℂ⁻¹)) := by
    refine ht.inv₀ ?_
    unfold riordanSqrtPlusAtOneℂ
    norm_num
  have htinvO : (fun u : ℂ => (t u)⁻¹)
      =O[𝓝 (0 : ℂ)] (fun _ : ℂ => (1 : ℝ)) :=
    tendsto_isBigO_one_complex htinv
  have hfinal := hone_minus.mul htinvO
  refine hfinal.congr' ?_ ?_
  · have ht_ne : ∀ᶠ u : ℂ in 𝓝 (0 : ℂ), t u ≠ 0 := by
      exact ht.eventually_ne (by
        unfold riordanSqrtPlusAtOneℂ
        norm_num)
    filter_upwards [ht_ne] with u hu
    dsimp [t, q] at hu ⊢
    field_simp [hu]
  · filter_upwards with u
    ring

lemma riordanSingularPartTaylorFull_sub_trunc (u : ℂ) :
    riordanSingularPartTaylorFull u -
        (riordanSingularCoeff + riordanSecondSingularCoeff * u +
          riordanThirdSingularCoeff * u ^ 2) =
      u ^ 3 * (riordanSingularCoeff * ((19 / 128 : ℂ) + (3 / 128 : ℂ) * u)) := by
  unfold riordanSingularPartTaylorFull riordanOneSubInvTaylor riordanSqrtPlusInvTaylor
    riordanThirdSingularCoeff riordanSecondSingularCoeff riordanSingularCoeff
  norm_num [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_neg]
  ring

lemma riordanSingularPartTaylorFull_sub_trunc_isBigO :
    (fun u : ℂ =>
      riordanSingularPartTaylorFull u -
        (riordanSingularCoeff + riordanSecondSingularCoeff * u +
          riordanThirdSingularCoeff * u ^ 2))
      =O[𝓝 (0 : ℂ)] (fun u : ℂ => ‖u‖ ^ 3) := by
  have hbase := cubic_mul_continuous_isBigO
    (fun u : ℂ => riordanSingularCoeff * ((19 / 128 : ℂ) + (3 / 128 : ℂ) * u))
    (by fun_prop)
  refine hbase.congr_left ?_
  intro u
  rw [riordanSingularPartTaylorFull_sub_trunc]

lemma riordanSingularPart_remainder_isBigO :
    (fun u : ℂ =>
      riordanSingularPart (1 - u) -
        (riordanSingularCoeff + riordanSecondSingularCoeff * u +
          riordanThirdSingularCoeff * u ^ 2))
      =O[𝓝 (0 : ℂ)] (fun u : ℂ => ‖u‖ ^ 3) := by
  let t : ℂ → ℂ := fun u => riordanSqrtPlus (1 - u)
  let oneInv : ℂ → ℂ := fun u => (1 - u)⁻¹
  let sqrtInv : ℂ → ℂ := fun u => (t u)⁻¹
  let oneTaylor : ℂ → ℂ := riordanOneSubInvTaylor
  let sqrtTaylor : ℂ → ℂ := riordanSqrtPlusInvTaylor
  have harg : Tendsto (fun u : ℂ => 1 - u) (𝓝 (0 : ℂ)) (𝓝 (1 : ℂ)) := by
    simpa using
      (continuousAt_const.sub continuousAt_id :
        ContinuousAt (fun u : ℂ => 1 - u) 0).tendsto
  have ht : Tendsto t (𝓝 (0 : ℂ)) (𝓝 riordanSqrtPlusAtOneℂ) := by
    simpa [t, riordanSqrtPlus_one] using
      hasDerivAt_riordanSqrtPlus_one.continuousAt.tendsto.comp harg
  have hsInvO : sqrtInv =O[𝓝 (0 : ℂ)] (fun _ : ℂ => (1 : ℝ)) := by
    have htinv : Tendsto sqrtInv (𝓝 (0 : ℂ)) (𝓝 (riordanSqrtPlusAtOneℂ⁻¹)) := by
      refine ht.inv₀ ?_
      unfold riordanSqrtPlusAtOneℂ
      norm_num
    exact tendsto_isBigO_one_complex htinv
  have hOneDiff : (fun u : ℂ => oneInv u - oneTaylor u)
      =O[𝓝 (0 : ℂ)] (fun u : ℂ => ‖u‖ ^ 3) := by
    simpa [oneInv, oneTaylor] using riordanOneSubInv_sub_taylor_isBigO
  have hTermOne := hOneDiff.mul hsInvO
  have hOneTaylorO : oneTaylor =O[𝓝 (0 : ℂ)] (fun _ : ℂ => (1 : ℝ)) := by
    have hcont : ContinuousAt oneTaylor 0 := by
      unfold oneTaylor riordanOneSubInvTaylor
      fun_prop
    exact tendsto_isBigO_one_complex hcont.tendsto
  have hSqrtDiff : (fun u : ℂ => sqrtInv u - sqrtTaylor u)
      =O[𝓝 (0 : ℂ)] (fun u : ℂ => ‖u‖ ^ 3) := by
    simpa [sqrtInv, sqrtTaylor, t] using riordanSqrtPlusInv_sub_taylor_isBigO
  have hTermTwo := hOneTaylorO.mul hSqrtDiff
  have hTermTwo' : (fun u : ℂ => oneTaylor u * (sqrtInv u - sqrtTaylor u))
      =O[𝓝 (0 : ℂ)] (fun u : ℂ => ‖u‖ ^ 3 * 1) := by
    refine hTermTwo.congr_right ?_
    intro u
    ring
  have hprodDiff : (fun u : ℂ =>
      oneInv u * sqrtInv u - oneTaylor u * sqrtTaylor u)
      =O[𝓝 (0 : ℂ)] (fun u : ℂ => ‖u‖ ^ 3) := by
    have hsum := hTermOne.add hTermTwo'
    exact (hsum.congr_left (by intro u; ring)).congr_right (by intro u; ring)
  have hscaled : (fun u : ℂ =>
      -(3 / 2 : ℂ) * (oneInv u * sqrtInv u - oneTaylor u * sqrtTaylor u))
      =O[𝓝 (0 : ℂ)] (fun u : ℂ => ‖u‖ ^ 3) :=
    hprodDiff.const_mul_left (-(3 / 2 : ℂ))
  have hsum := hscaled.add riordanSingularPartTaylorFull_sub_trunc_isBigO
  refine hsum.congr' ?_ (EventuallyEq.refl _ _)
  have ht_ne : ∀ᶠ u : ℂ in 𝓝 (0 : ℂ), t u ≠ 0 := by
    exact ht.eventually_ne (by
      unfold riordanSqrtPlusAtOneℂ
      norm_num)
  filter_upwards [eventually_ne_nhds (show (0 : ℂ) ≠ 1 by norm_num), ht_ne] with u hu1 ht0
  dsimp [oneInv, sqrtInv, oneTaylor, sqrtTaylor, t]
  unfold riordanSingularPart riordanSingularPartTaylorFull
  field_simp [sub_ne_zero.mpr (Ne.symm hu1), ht0]
  ring

lemma riordanSqrtOneSub_local_isBigO :
    (fun u : ℂ => riordanSqrtOneSub (1 - u)) =O[𝓝 (0 : ℂ)]
      (fun u : ℂ => ‖u‖ ^ (1 / 2 : ℝ)) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards with u
  unfold riordanSqrtOneSub motzkinSqrtOneSub
  rw [show (1 : ℂ) - (1 - u) = u by ring]
  rw [show (1 / 2 : ℂ) = (((1 / 2 : ℝ) : ℂ)) by norm_num]
  rw [Complex.norm_cpow_real u (1 / 2 : ℝ)]
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg u) _)]
  simp

lemma riordanThird_local_residual_eq {u : ℂ}
    (hu1 : u ≠ 1) (hznorm : ‖(1 : ℂ) - u‖ < 3) :
    sqrtAdjustedFun riordanThirdAdjustedRescaledFun riordanRegularValueℂ
        (-riordanAnalyticLinearCoeff) (1 - u) -
        riordanSingularCoeff * u ^ (1 / 2 : ℂ) -
        riordanSecondSingularCoeff * u ^ (3 / 2 : ℂ) -
        riordanThirdSingularCoeff * u ^ (5 / 2 : ℂ) =
      (riordanAnalyticPart (1 - u) -
        (riordanRegularValueℂ + riordanAnalyticLinearCoeff * u +
          riordanAnalyticQuadraticCoeff * u ^ 2)) +
        (riordanSingularPart (1 - u) -
          (riordanSingularCoeff + riordanSecondSingularCoeff * u +
            riordanThirdSingularCoeff * u ^ 2)) *
          riordanSqrtOneSub (1 - u) := by
  have hz_ne : (1 : ℂ) - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu1)
  have hdecomp := riordanRescaledFun_decomp (z := 1 - u) hz_ne hznorm
  have hs : riordanSqrtOneSub (1 - u) = u ^ (1 / 2 : ℂ) := by
    unfold riordanSqrtOneSub motzkinSqrtOneSub
    rw [show (1 : ℂ) - (1 - u) = u by ring]
  have hpow3 : u ^ (3 / 2 : ℂ) = u * riordanSqrtOneSub (1 - u) := by
    by_cases hu0 : u = 0
    · subst u
      norm_num [riordanSqrtOneSub, motzkinSqrtOneSub]
    · rw [hs]
      rw [show (3 / 2 : ℂ) = 1 + (1 / 2 : ℂ) by norm_num]
      rw [Complex.cpow_add _ _ hu0, Complex.cpow_one]
  have hpow5 : u ^ (5 / 2 : ℂ) = u ^ 2 * riordanSqrtOneSub (1 - u) := by
    by_cases hu0 : u = 0
    · subst u
      norm_num [riordanSqrtOneSub, motzkinSqrtOneSub]
    · rw [hs]
      rw [show (5 / 2 : ℂ) = 2 + (1 / 2 : ℂ) by norm_num]
      rw [Complex.cpow_add _ _ hu0]
      norm_num [Complex.cpow_natCast]
  unfold sqrtAdjustedFun sqrtLinearAtOneFun riordanThirdAdjustedRescaledFun
  rw [hdecomp, hpow3, hpow5, hs]
  ring

lemma riordanThird_local_residual_isLittleO :
    (fun u : ℂ =>
      sqrtAdjustedFun riordanThirdAdjustedRescaledFun riordanRegularValueℂ
          (-riordanAnalyticLinearCoeff) (1 - u) -
          riordanSingularCoeff * u ^ (1 / 2 : ℂ) -
          riordanSecondSingularCoeff * u ^ (3 / 2 : ℂ) -
          riordanThirdSingularCoeff * u ^ (5 / 2 : ℂ))
      =o[𝓝 (0 : ℂ)] (fun u : ℂ => ‖u‖ ^ (5 / 2 : ℝ)) := by
  have hA := riordanAnalyticPart_remainder_isBigO.trans_isLittleO
    norm_pow_three_isLittleO_norm_rpow_five_halves
  have hBbig := riordanSingularPart_remainder_isBigO.mul
    riordanSqrtOneSub_local_isBigO
  have hB := hBbig.trans_isLittleO
    norm_pow_three_mul_rpow_half_isLittleO_norm_rpow_five_halves
  have hsum := hA.add hB
  refine hsum.congr' ?_ (EventuallyEq.refl _ _)
  have hnorm : ∀ᶠ u : ℂ in 𝓝 (0 : ℂ), ‖(1 : ℂ) - u‖ < 3 := by
    have hcont : ContinuousAt (fun u : ℂ => ‖(1 : ℂ) - u‖) 0 := by
      fun_prop
    exact hcont.tendsto.eventually (Iio_mem_nhds (by norm_num : ‖(1 : ℂ) - 0‖ < 3))
  filter_upwards [eventually_ne_nhds (show (0 : ℂ) ≠ 1 by norm_num), hnorm] with u hu1 hzu
  simpa using (riordanThird_local_residual_eq (u := u) hu1 hzu).symm

lemma tendsto_riordanThirdAdjustedRescaledFun_singularity :
    Tendsto
      (fun z : ℂ =>
        ‖sqrtAdjustedFun riordanThirdAdjustedRescaledFun riordanRegularValueℂ
            (-riordanAnalyticLinearCoeff) z -
            riordanSingularCoeff * (1 - z) ^ (1 / 2 : ℂ) -
            riordanSecondSingularCoeff * (1 - z) ^ (3 / 2 : ℂ) -
            riordanThirdSingularCoeff * (1 - z) ^ (5 / 2 : ℂ)‖ *
          ‖(1 : ℂ) - z‖ ^ (-(5 / 2 : ℝ)))
      (𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)) (𝓝 0) := by
  let l := 𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)
  have hu : Tendsto (fun z : ℂ => 1 - z) l (𝓝 (0 : ℂ)) := by
    have hcont : ContinuousAt (fun z : ℂ => 1 - z) 1 := by fun_prop
    simpa using Tendsto.mono_left hcont.tendsto nhdsWithin_le_nhds
  have hcomp := riordanThird_local_residual_isLittleO.comp_tendsto hu
  have hdiv := hcomp.norm_norm.tendsto_div_nhds_zero
  refine hdiv.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz_ne : z ≠ 1 := hz.2.1
  have hpos : 0 < ‖(1 : ℂ) - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hz_ne))
  rw [div_eq_mul_inv]
  dsimp only [Function.comp_apply]
  rw [show (1 : ℂ) - (1 - z) = z by ring]
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg ((1 : ℂ) - z)) _)]
  rw [Real.rpow_neg hpos.le]

lemma riordanSecondSingularCoeff_eq_meta :
    riordanSecondSingularCoeff =
      -(((riordanRho : ℝ) : ℂ) * riordanSingularDerivAtRho) := by
  unfold riordanSecondSingularCoeff riordanSingularCoeff riordanRho
    riordanSingularDerivAtRho
  norm_num [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_neg]
  ring

lemma riordanThirdSingularCoeff_eq_meta :
    riordanThirdSingularCoeff =
      ((((riordanRho : ℝ) : ℂ) ^ 2 * riordanSingularSecondDerivAtRho) / 2) := by
  unfold riordanThirdSingularCoeff riordanRho riordanSingularSecondDerivAtRho
  norm_num [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_neg]
  ring

lemma riordanThirdAsymptoticConstant_eq_meta :
    sqrtSingularityC2 riordanRho riordanSingularCoeff
        riordanSingularDerivAtRho riordanSingularSecondDerivAtRho =
      ((riordanThirdAsymptoticConstant : ℝ) : ℂ) := by
  unfold sqrtSingularityC2 sqrtSingularityC2Rescaled riordanRho riordanSingularCoeff
    riordanSingularDerivAtRho riordanSingularSecondDerivAtRho
    riordanThirdAsymptoticConstant
  norm_num [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_neg]
  ring

lemma riordanFirstAsymptoticConstant_eq_meta :
    sqrtSingularityC0 riordanSingularCoeff =
      ((riordanAsymptoticConstant : ℝ) : ℂ) := by
  unfold sqrtSingularityC0 riordanSingularCoeff riordanAsymptoticConstant
  norm_num [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_neg]
  ring

lemma riordanSecondAsymptoticConstant_eq_meta :
    sqrtSingularityC1 riordanRho riordanSingularCoeff riordanSingularDerivAtRho =
      ((riordanSecondAsymptoticConstant : ℝ) : ℂ) := by
  unfold sqrtSingularityC1 sqrtSingularityC1Rescaled riordanRho riordanSingularCoeff
    riordanSingularDerivAtRho riordanSecondAsymptoticConstant
  norm_num [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_neg]
  ring

lemma riordanSingularCoeff_ne_zero : riordanSingularCoeff ≠ 0 := by
  unfold riordanSingularCoeff
  norm_num

theorem riordanThirdOriginalSeries_complex_meta :
    (fun n : ℕ =>
      PowerSeries.coeff (R := ℂ) n riordanThirdOriginalSeriesℂ -
        (((((riordanRho : ℝ) : ℂ)⁻¹) ^ n) *
          (sqrtSingularityC0 riordanSingularCoeff *
              (((n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) +
            sqrtSingularityC1 riordanRho riordanSingularCoeff riordanSingularDerivAtRho *
              (((n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ) +
            sqrtSingularityC2 riordanRho riordanSingularCoeff
                riordanSingularDerivAtRho riordanSingularSecondDerivAtRho *
              (((n : ℝ) ^ (-(7 / 2 : ℝ)) : ℝ) : ℂ))))
      =o[atTop]
        (fun n : ℕ =>
          ‖(((((riordanRho : ℝ) : ℂ)⁻¹) ^ n) *
            (((n : ℝ) ^ (-(7 / 2 : ℝ)) : ℝ) : ℂ))‖) := by
  refine sqrt_singularity_thirdOrder_original_of_rescaled_singularity
    (ρ := riordanRho) (R := (3 / 2 : ℝ)) (φ := Real.pi / 4)
    (F := riordanThirdOriginalFun) (P := riordanThirdOriginalSeriesℂ)
    (A0 := riordanRegularValueℂ) (A1 := -riordanAnalyticLinearCoeff)
    (Bρ := riordanSingularCoeff)
    (Bderivρ := riordanSingularDerivAtRho)
    (Bsecondρ := riordanSingularSecondDerivAtRho)
    ?_ riordanSingularCoeff_ne_zero ?_ ?_ ?_
    riordanThirdOriginalFun_rescaled_hasFPowerSeriesAt_zero
    analyticOnNhd_riordanThirdOriginalFun_rescaled ?_
  · unfold riordanRho
    norm_num
  · norm_num
  · positivity
  · nlinarith [Real.pi_pos]
  · have h := tendsto_riordanThirdAdjustedRescaledFun_singularity
    have hrescale : ∀ w : ℂ,
        riordanThirdOriginalFun (((riordanRho : ℝ) : ℂ) * w) =
          riordanThirdAdjustedRescaledFun w :=
      riordanThirdOriginalFun_rescale
    have hrescale3 : ∀ w : ℂ,
        riordanThirdOriginalFun ((3 : ℂ)⁻¹ * w) =
          riordanThirdAdjustedRescaledFun w := by
      intro w
      have hρ : (((riordanRho : ℝ) : ℂ)) = (3 : ℂ)⁻¹ := by
        unfold riordanRho
        norm_num
      rw [← hρ]
      exact hrescale w
    refine h.congr' ?_
    filter_upwards with z
    simp [sqrtAdjustedFun, hrescale, riordanSecondSingularCoeff_eq_meta,
      riordanThirdSingularCoeff_eq_meta]

lemma riordanOneSubThreeXSeries_sq_coeff_of_three_le {n : ℕ} (hn : 3 ≤ n) :
    PowerSeries.coeff (R := ℂ) n (riordanOneSubThreeXSeriesℂ ^ 2) = 0 := by
  rw [pow_two, PowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  rcases p with ⟨i, j⟩
  have hij : i + j = n := Finset.mem_antidiagonal.mp hp
  have hlarge : 2 ≤ i ∨ 2 ≤ j := by
    by_contra h
    push Not at h
    have hi : i ≤ 1 := Nat.lt_succ_iff.mp h.1
    have hj : j ≤ 1 := Nat.lt_succ_iff.mp h.2
    omega
  rcases hlarge with hi | hj
  · have hcoeff : PowerSeries.coeff (R := ℂ) i riordanOneSubThreeXSeriesℂ = 0 := by
      unfold riordanOneSubThreeXSeriesℂ
      simp [PowerSeries.coeff_X,
        ne_of_gt (lt_of_lt_of_le (by norm_num : 0 < 2) hi),
        ne_of_gt (lt_of_lt_of_le (by norm_num : 1 < 2) hi)]
    simp [hcoeff]
  · have hcoeff : PowerSeries.coeff (R := ℂ) j riordanOneSubThreeXSeriesℂ = 0 := by
      unfold riordanOneSubThreeXSeriesℂ
      simp [PowerSeries.coeff_X,
        ne_of_gt (lt_of_lt_of_le (by norm_num : 0 < 2) hj),
        ne_of_gt (lt_of_lt_of_le (by norm_num : 1 < 2) hj)]
    simp [hcoeff]

lemma coeff_riordanThirdOriginalSeriesℂ_of_three_le {n : ℕ} (hn : 3 ≤ n) :
    PowerSeries.coeff (R := ℂ) n riordanThirdOriginalSeriesℂ = (riordan n : ℂ) := by
  unfold riordanThirdOriginalSeriesℂ
  simp [PowerSeries.coeff_C_mul, riordanOneSubThreeXSeries_sq_coeff_of_three_le hn]

private lemma complex_re_isLittleO_ofReal {f : ℕ → ℂ} {g r : ℕ → ℝ}
    (h : (fun n : ℕ => f n - ((g n : ℝ) : ℂ)) =o[atTop] r) :
    (fun n : ℕ => (f n).re - g n) =o[atTop] r := by
  rw [Asymptotics.isLittleO_iff] at h ⊢
  intro c hc
  have hc_bound := h hc
  filter_upwards [hc_bound] with n hn
  calc
    ‖(f n).re - g n‖ = ‖(f n - (g n : ℂ)).re‖ := by
      simp [Complex.sub_re]
    _ ≤ ‖f n - (g n : ℂ)‖ := Complex.abs_re_le_norm _
    _ ≤ c * ‖r n‖ := hn

theorem riordan_complex_thirdOrder_additive :
    (fun n : ℕ =>
      (riordan n : ℂ) -
        (((((3 : ℝ) ^ n) *
          (riordanAsymptoticConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
            riordanSecondAsymptoticConstant * (n : ℝ) ^ (-(5 / 2 : ℝ)) +
            riordanThirdAsymptoticConstant * (n : ℝ) ^ (-(7 / 2 : ℝ))) : ℝ) : ℂ)))
      =o[atTop]
        (fun n : ℕ => (3 : ℝ) ^ n * (n : ℝ) ^ (-(7 / 2 : ℝ))) := by
  have h := riordanThirdOriginalSeries_complex_meta
  refine h.congr' ?_ ?_
  · filter_upwards [eventually_ge_atTop 3] with n hn
    rw [coeff_riordanThirdOriginalSeriesℂ_of_three_le hn]
    rw [riordanFirstAsymptoticConstant_eq_meta,
      riordanSecondAsymptoticConstant_eq_meta,
      riordanThirdAsymptoticConstant_eq_meta]
    have hρ : (((riordanRho : ℝ) : ℂ)⁻¹) ^ n = (((3 : ℝ) ^ n : ℝ) : ℂ) := by
      have hbase : (((riordanRho : ℝ) : ℂ)⁻¹) = ((3 : ℝ) : ℂ) := by
        unfold riordanRho
        norm_num
      rw [hbase, Complex.ofReal_pow]
    rw [hρ]
    norm_num [Complex.ofReal_mul, Complex.ofReal_add]
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : 0 < (n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ)) hn)
    have hρ : (((riordanRho : ℝ) : ℂ)⁻¹) ^ n = (((3 : ℝ) ^ n : ℝ) : ℂ) := by
      have hbase : (((riordanRho : ℝ) : ℂ)⁻¹) = ((3 : ℝ) : ℂ) := by
        unfold riordanRho
        norm_num
      rw [hbase, Complex.ofReal_pow]
    rw [hρ, norm_mul, Complex.norm_real, Complex.norm_real]
    rw [Real.norm_of_nonneg (by positivity : 0 ≤ (3 : ℝ) ^ n)]
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (le_of_lt hnpos) _)]

theorem riordan_thirdOrder_additive :
    (fun n : ℕ =>
      (riordan n : ℝ) -
        (3 : ℝ) ^ n *
          (riordanAsymptoticConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
            riordanSecondAsymptoticConstant * (n : ℝ) ^ (-(5 / 2 : ℝ)) +
            riordanThirdAsymptoticConstant * (n : ℝ) ^ (-(7 / 2 : ℝ))))
      =o[atTop]
        (fun n : ℕ => (3 : ℝ) ^ n * (n : ℝ) ^ (-(7 / 2 : ℝ))) := by
  have hcomplex :
      (fun n : ℕ =>
        (((riordan n : ℝ) : ℂ) -
          ((((3 : ℝ) ^ n *
            (riordanAsymptoticConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
              riordanSecondAsymptoticConstant * (n : ℝ) ^ (-(5 / 2 : ℝ)) +
              riordanThirdAsymptoticConstant * (n : ℝ) ^ (-(7 / 2 : ℝ))) : ℝ) : ℂ))))
        =o[atTop]
          (fun n : ℕ => (3 : ℝ) ^ n * (n : ℝ) ^ (-(7 / 2 : ℝ))) := by
    simpa [Complex.ofReal_mul, Complex.ofReal_add] using riordan_complex_thirdOrder_additive
  have hreal := complex_re_isLittleO_ofReal hcomplex
  simpa using hreal

lemma riordanThirdAsymptoticConstant_eq_relative :
    riordanThirdAsymptoticConstant =
      riordanAsymptoticConstant * riordanRelativeThirdConstant := by
  unfold riordanThirdAsymptoticConstant riordanAsymptoticConstant
    riordanRelativeThirdConstant
  ring

theorem riordan_thirdOrder :
    (fun n : ℕ =>
      (riordan n : ℝ) -
        (3 : ℝ) ^ n * riordanAsymptoticConstant *
          (n : ℝ) ^ (-(3 / 2 : ℝ)) *
          (1 + riordanRelativeSecondConstant * (n : ℝ) ^ (-(1 : ℝ)) +
            riordanRelativeThirdConstant * (n : ℝ) ^ (-(2 : ℝ))))
      =o[atTop]
        (fun n : ℕ => (3 : ℝ) ^ n * (n : ℝ) ^ (-(7 / 2 : ℝ))) := by
  refine riordan_thirdOrder_additive.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ)) hn)
  have hpow5 : (n : ℝ) ^ (-(5 / 2 : ℝ)) =
      (n : ℝ) ^ (-(3 / 2 : ℝ)) * (n : ℝ) ^ (-(1 : ℝ)) := by
    rw [← Real.rpow_add hnpos]
    norm_num
  have hpow7 : (n : ℝ) ^ (-(7 / 2 : ℝ)) =
      (n : ℝ) ^ (-(3 / 2 : ℝ)) * (n : ℝ) ^ (-(2 : ℝ)) := by
    rw [← Real.rpow_add hnpos]
    norm_num
  rw [riordanSecondAsymptoticConstant_eq_relative,
    riordanThirdAsymptoticConstant_eq_relative, hpow5, hpow7]
  ring

lemma riordanRelativeThirdConstant_eq_meta :
    sqrtSingularityRelativeC2 riordanSingularCoeff
        (((riordanRho : ℝ) : ℂ) * riordanSingularDerivAtRho)
        ((((riordanRho : ℝ) : ℂ) ^ 2) * riordanSingularSecondDerivAtRho) =
      (riordanRelativeThirdConstant : ℂ) := by
  unfold sqrtSingularityRelativeC2 riordanRho riordanSingularCoeff
    riordanSingularDerivAtRho riordanSingularSecondDerivAtRho
    riordanRelativeThirdConstant
  norm_num [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_neg]
  have hs3 : ((Real.sqrt 3 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 3))
  field_simp [hs3]
  norm_num

end
