import AnalyticCombinatorics.Ch4.Analytic.SqrtSingularityThirdOrder
import AnalyticCombinatorics.Ch7.SingularityApp.MotzkinSecondOrder

/-!
# Third-order Motzkin asymptotics

This file plugs the Motzkin square-root data at `ρ = 1 / 3` into the
third-order square-root applicator.
-/

set_option maxHeartbeats 1200000

open Complex Filter Asymptotics Set
open scoped Topology BigOperators PowerSeries

noncomputable section

def motzkinRho : ℝ := 1 / 3

def motzkinAnalyticQuadraticCoeff : ℂ := 12

def motzkinSingularDerivAtRho : ℂ :=
  (((135 * Real.sqrt 3 / 8 : ℝ) : ℂ))

def motzkinSingularSecondDerivAtRho : ℂ :=
  -(((9477 * Real.sqrt 3 / 64 : ℝ) : ℂ))

def motzkinThirdSingularCoeff : ℂ :=
  ((((motzkinRho : ℝ) : ℂ) ^ 2 * motzkinSingularSecondDerivAtRho) / 2)

def motzkinThirdAsymptoticConstant : ℝ :=
  7995 * Real.sqrt 3 / (1024 * Real.sqrt Real.pi)

def motzkinRelativeThirdConstant : ℝ := 2665 / 512

def motzkinOneSubThreeXSeriesℂ : PowerSeries ℂ :=
  (1 : PowerSeries ℂ) - PowerSeries.C (3 : ℂ) * PowerSeries.X

def motzkinThirdOriginalSeriesℂ : PowerSeries ℂ :=
  motzkinSeriesℂ -
    PowerSeries.C motzkinAnalyticQuadraticCoeff * motzkinOneSubThreeXSeriesℂ ^ 2

def motzkinThirdAdjustedRescaledSeriesℂ : PowerSeries ℂ :=
  motzkinRescaledSeriesℂ -
    PowerSeries.C motzkinAnalyticQuadraticCoeff * motzkinOneSubSeriesℂ ^ 2

def motzkinOriginalFun (z : ℂ) : ℂ :=
  motzkinRescaledFun (3 * z)

def motzkinThirdOriginalFun (z : ℂ) : ℂ :=
  motzkinOriginalFun z - motzkinAnalyticQuadraticCoeff * (1 - 3 * z) ^ 2

def motzkinThirdAdjustedRescaledFun (z : ℂ) : ℂ :=
  motzkinRescaledFun z - motzkinAnalyticQuadraticCoeff * (1 - z) ^ 2

lemma motzkinThirdOriginalFun_rescale (z : ℂ) :
    motzkinThirdOriginalFun (((motzkinRho : ℝ) : ℂ) * z) =
      motzkinThirdAdjustedRescaledFun z := by
  unfold motzkinThirdOriginalFun motzkinOriginalFun motzkinThirdAdjustedRescaledFun
    motzkinRho motzkinAnalyticQuadraticCoeff
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

lemma rescale_motzkinOneSubThreeXSeriesℂ :
    PowerSeries.rescale (((motzkinRho : ℝ) : ℂ)) motzkinOneSubThreeXSeriesℂ =
      motzkinOneSubSeriesℂ := by
  ext n
  rw [PowerSeries.coeff_rescale]
  cases n with
  | zero =>
      simp [motzkinOneSubThreeXSeriesℂ, motzkinOneSubSeriesℂ]
  | succ n =>
      cases n with
      | zero =>
          simp [motzkinOneSubThreeXSeriesℂ, motzkinOneSubSeriesℂ, motzkinRho,
            PowerSeries.coeff_X, PowerSeries.coeff_C]
      | succ n =>
          simp [motzkinOneSubThreeXSeriesℂ, motzkinOneSubSeriesℂ, PowerSeries.coeff_X]

lemma rescale_motzkinThirdOriginalSeriesℂ :
    PowerSeries.rescale (((motzkinRho : ℝ) : ℂ)) motzkinThirdOriginalSeriesℂ =
      motzkinThirdAdjustedRescaledSeriesℂ := by
  unfold motzkinThirdOriginalSeriesℂ motzkinThirdAdjustedRescaledSeriesℂ
  simp only [map_sub, map_mul, map_pow,
    rescale_motzkinOneSubThreeXSeriesℂ]
  rw [PowerSeries_rescale_C]
  have hρ : (((motzkinRho : ℝ) : ℂ)) = (3 : ℂ)⁻¹ := by
    unfold motzkinRho
    norm_num
  rw [hρ]
  rfl

lemma motzkinThirdAdjustedRescaledFun_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt motzkinThirdAdjustedRescaledFun
      (PowerSeries.toFMLS motzkinThirdAdjustedRescaledSeriesℂ) (0 : ℂ) := by
  have hsquare : HasFPowerSeriesAt (fun z : ℂ => (1 - z) * (1 - z))
      (PowerSeries.toFMLS (motzkinOneSubSeriesℂ ^ 2)) (0 : ℂ) := by
    simpa [pow_two] using
      hasFPowerSeriesAt_mul_toFMLS hasFPowerSeriesAt_one_sub_toFMLS
        hasFPowerSeriesAt_one_sub_toFMLS
  have hquad : HasFPowerSeriesAt
      (fun z : ℂ => motzkinAnalyticQuadraticCoeff * (1 - z) ^ 2)
      (PowerSeries.toFMLS
        (PowerSeries.C motzkinAnalyticQuadraticCoeff * motzkinOneSubSeriesℂ ^ 2))
      (0 : ℂ) := by
    have h := hsquare.const_smul (c := motzkinAnalyticQuadraticCoeff)
    convert h using 1
    · ext z
      simp [pow_two, smul_eq_mul]
    · ext n
      simp [PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars,
        PowerSeries.coeff_C_mul]
  have hsub := motzkinRescaledFun_hasFPowerSeriesAt_zero.sub hquad
  simpa [motzkinThirdAdjustedRescaledFun, motzkinThirdAdjustedRescaledSeriesℂ,
    toFMLS_sub] using hsub

lemma motzkinThirdOriginalFun_rescaled_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt
      (fun z : ℂ => motzkinThirdOriginalFun (((motzkinRho : ℝ) : ℂ) * z))
      (PowerSeries.toFMLS
        (PowerSeries.rescale (((motzkinRho : ℝ) : ℂ)) motzkinThirdOriginalSeriesℂ))
      (0 : ℂ) := by
  rw [rescale_motzkinThirdOriginalSeriesℂ]
  simpa [motzkinThirdOriginalFun_rescale] using
    motzkinThirdAdjustedRescaledFun_hasFPowerSeriesAt_zero

lemma analyticOnNhd_motzkinThirdAdjustedRescaledFun :
    AnalyticOnNhd ℂ motzkinThirdAdjustedRescaledFun
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
  have hquad : AnalyticOnNhd ℂ
      (fun z : ℂ => motzkinAnalyticQuadraticCoeff * (1 - z) ^ 2)
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
    simpa [pow_two] using
      (analyticOnNhd_const.mul
        ((analyticOnNhd_const.sub analyticOnNhd_id).mul
          (analyticOnNhd_const.sub analyticOnNhd_id)))
  simpa [motzkinThirdAdjustedRescaledFun] using
    analyticOnNhd_motzkinRescaledFun.sub hquad

lemma analyticOnNhd_motzkinThirdOriginalFun_rescaled :
    AnalyticOnNhd ℂ
      (fun z : ℂ => motzkinThirdOriginalFun (((motzkinRho : ℝ) : ℂ) * z))
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
  simpa [motzkinThirdOriginalFun_rescale] using
    analyticOnNhd_motzkinThirdAdjustedRescaledFun

def motzkinAnalyticPart (z : ℂ) : ℂ :=
  (9 / 2 : ℂ) * (1 - z / 3) / z ^ 2

def motzkinSingularPart (z : ℂ) : ℂ :=
  -(9 / 2 : ℂ) * motzkinSqrtPlus z / z ^ 2

def motzkinSqrtPlusTaylor (u : ℂ) : ℂ :=
  (((2 / Real.sqrt 3 : ℝ) : ℂ)) * (1 - u / 8 - u ^ 2 / 128)

def motzkinSqrtPlusBTaylor (u : ℂ) : ℂ :=
  -(2 / 9 : ℂ) *
    (motzkinSingularCoeff + motzkinSecondSingularCoeff * u +
      motzkinThirdSingularCoeff * u ^ 2) * (1 - u) ^ 2

lemma motzkinRescaledFun_decomp {z : ℂ} (hz : z ≠ 0) :
    motzkinRescaledFun z =
      motzkinAnalyticPart z + motzkinSingularPart z * motzkinSqrtOneSub z := by
  unfold motzkinRescaledFun
  rw [div_eq_iff (motzkinRescaledDenominator_ne_zero z)]
  unfold motzkinAnalyticPart motzkinSingularPart motzkinRescaledDenominator
  field_simp [hz]
  ring_nf
  rw [motzkinSqrtOneSub_sq]
  unfold motzkinSqrtPlus
  rw [Complex_cpow_half_sq]
  ring_nf

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

lemma motzkinSqrtPlus_sq_sub_taylor_sq (u : ℂ) :
    (motzkinSqrtPlus (1 - u)) ^ 2 - (motzkinSqrtPlusTaylor u) ^ 2 =
      -u ^ 3 * (32 + u) / 12288 := by
  unfold motzkinSqrtPlus motzkinSqrtPlusTaylor
  rw [Complex_cpow_half_sq]
  norm_num [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_sub]
  field_simp
  ring_nf
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num
  ring_nf

lemma motzkinSqrtPlus_sub_taylor_isBigO :
    (fun u : ℂ => motzkinSqrtPlus (1 - u) - motzkinSqrtPlusTaylor u)
      =O[𝓝 (0 : ℂ)] (fun u : ℂ => ‖u‖ ^ 3) := by
  let t : ℂ → ℂ := fun u => motzkinSqrtPlus (1 - u)
  let q : ℂ → ℂ := motzkinSqrtPlusTaylor
  have ht : Tendsto t (𝓝 (0 : ℂ)) (𝓝 (((2 / Real.sqrt 3 : ℝ) : ℂ))) := by
    have harg : Tendsto (fun u : ℂ => 1 - u) (𝓝 (0 : ℂ)) (𝓝 (1 : ℂ)) := by
      simpa using (continuousAt_const.sub continuousAt_id : ContinuousAt (fun u : ℂ => 1 - u) 0).tendsto
    have h := hasDerivAt_motzkinSqrtPlus_one.continuousAt.tendsto.comp harg
    simpa [t, motzkinSqrtPlus_one] using h
  have hq : Tendsto q (𝓝 (0 : ℂ)) (𝓝 (((2 / Real.sqrt 3 : ℝ) : ℂ))) := by
    have hcont : ContinuousAt q 0 := by
      unfold q motzkinSqrtPlusTaylor
      fun_prop
    simpa [q, motzkinSqrtPlusTaylor] using hcont.tendsto
  have hden : Tendsto (fun u : ℂ => (t u + q u)⁻¹) (𝓝 (0 : ℂ))
      (𝓝 (((((2 / Real.sqrt 3 : ℝ) : ℂ)) +
        (((2 / Real.sqrt 3 : ℝ) : ℂ)))⁻¹)) := by
    refine (ht.add hq).inv₀ ?_
    have hs3 : ((Real.sqrt 3 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 3))
    norm_num [Complex.ofReal_div]
  have hdenO : (fun u : ℂ => (t u + q u)⁻¹) =O[𝓝 (0 : ℂ)]
      (fun _ : ℂ => (1 : ℝ)) :=
    tendsto_isBigO_one_complex hden
  have hsqO : (fun u : ℂ => (t u) ^ 2 - (q u) ^ 2) =O[𝓝 (0 : ℂ)]
      (fun u : ℂ => ‖u‖ ^ 3) := by
    have hbase := cubic_mul_continuous_isBigO
      (fun u : ℂ => -(32 + u) / 12288)
      (by fun_prop)
    refine hbase.congr_left ?_
    intro u
    rw [motzkinSqrtPlus_sq_sub_taylor_sq]
    ring
  have hprod := hsqO.mul hdenO
  refine hprod.congr' ?_ ?_
  · have hsum_ne : ∀ᶠ u : ℂ in 𝓝 (0 : ℂ), t u + q u ≠ 0 := by
      have hsum := ht.add hq
      refine hsum.eventually_ne ?_
      have hs3 : ((Real.sqrt 3 : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 3))
      norm_num [Complex.ofReal_div]
    filter_upwards [hsum_ne] with u hu
    dsimp [t, q] at hu ⊢
    set a := motzkinSqrtPlus (1 - u)
    set b := motzkinSqrtPlusTaylor u
    rw [show a ^ 2 - b ^ 2 = (a - b) * (a + b) by ring]
    rw [mul_assoc, mul_inv_cancel₀ hu, mul_one]
  · filter_upwards with u
    ring

lemma motzkinAnalyticPart_remainder_isBigO :
    (fun u : ℂ =>
      motzkinAnalyticPart (1 - u) -
        (3 + motzkinAnalyticLinearCoeff * u + motzkinAnalyticQuadraticCoeff * u ^ 2))
      =O[𝓝 (0 : ℂ)] (fun u : ℂ => ‖u‖ ^ 3) := by
  have hbase := cubic_mul_continuous_isBigO
    (fun u : ℂ => ((33 / 2 : ℂ) - 12 * u) / (1 - u) ^ 2)
    (by
      apply ContinuousAt.div
      · fun_prop
      · fun_prop
      · norm_num)
  refine hbase.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_ne_nhds (show (0 : ℂ) ≠ 1 by norm_num)] with u hu
  unfold motzkinAnalyticPart motzkinAnalyticLinearCoeff motzkinAnalyticQuadraticCoeff
  field_simp [sub_ne_zero.mpr (Ne.symm hu)]
  ring

lemma motzkinSqrtPlusTaylor_sub_BTaylor_isBigO :
    (fun u : ℂ => motzkinSqrtPlusTaylor u - motzkinSqrtPlusBTaylor u)
      =O[𝓝 (0 : ℂ)] (fun u : ℂ => ‖u‖ ^ 3) := by
  have hbase := cubic_mul_continuous_isBigO
    (fun u : ℂ => (((2 / Real.sqrt 3 : ℝ) : ℂ)) *
      ((231 / 64 : ℂ) - (351 / 128 : ℂ) * u))
    (by fun_prop)
  refine hbase.congr_left ?_
  intro u
  unfold motzkinSqrtPlusTaylor motzkinSqrtPlusBTaylor motzkinSingularCoeff
    motzkinSecondSingularCoeff motzkinThirdSingularCoeff motzkinRho
    motzkinSingularSecondDerivAtRho
  have hs3 : ((Real.sqrt 3 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 3))
  field_simp [hs3]
  ring_nf
  norm_num [Complex.ofReal_div, Complex.ofReal_mul] at *
  field_simp [hs3]
  ring_nf
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num
  ring_nf

lemma motzkinSingularPart_remainder_isBigO :
    (fun u : ℂ =>
      motzkinSingularPart (1 - u) -
        (motzkinSingularCoeff + motzkinSecondSingularCoeff * u +
          motzkinThirdSingularCoeff * u ^ 2))
      =O[𝓝 (0 : ℂ)] (fun u : ℂ => ‖u‖ ^ 3) := by
  have hdiff : (fun u : ℂ => motzkinSqrtPlus (1 - u) - motzkinSqrtPlusBTaylor u)
      =O[𝓝 (0 : ℂ)] (fun u : ℂ => ‖u‖ ^ 3) := by
    have hsum := motzkinSqrtPlus_sub_taylor_isBigO.add
      motzkinSqrtPlusTaylor_sub_BTaylor_isBigO
    refine hsum.congr_left ?_
    intro u
    ring
  have hden_tendsto : Tendsto (fun u : ℂ => ((1 - u) ^ 2)⁻¹) (𝓝 (0 : ℂ)) (𝓝 (1 : ℂ)) := by
    have hcont : ContinuousAt (fun u : ℂ => (1 - u) ^ 2) 0 := by fun_prop
    have hne : ((1 - (0 : ℂ)) ^ 2) ≠ 0 := by norm_num
    convert hcont.tendsto.inv₀ hne using 1
    norm_num
  have hdenO : (fun u : ℂ => ((1 - u) ^ 2)⁻¹) =O[𝓝 (0 : ℂ)]
      (fun _ : ℂ => (1 : ℝ)) :=
    tendsto_isBigO_one_complex hden_tendsto
  have hprod := hdiff.mul hdenO
  have hscaled : (fun u : ℂ =>
      (-(9 / 2 : ℂ)) *
        ((motzkinSqrtPlus (1 - u) - motzkinSqrtPlusBTaylor u) * ((1 - u) ^ 2)⁻¹))
      =O[𝓝 (0 : ℂ)] (fun u : ℂ => ‖u‖ ^ 3) := by
    refine (hprod.const_mul_left (-(9 / 2 : ℂ))).congr_right ?_
    intro u
    ring
  refine hscaled.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_ne_nhds (show (0 : ℂ) ≠ 1 by norm_num)] with u hu
  unfold motzkinSingularPart motzkinSqrtPlusBTaylor
  field_simp [sub_ne_zero.mpr (Ne.symm hu)]
  ring

lemma motzkinSqrtOneSub_local_isBigO :
    (fun u : ℂ => motzkinSqrtOneSub (1 - u)) =O[𝓝 (0 : ℂ)]
      (fun u : ℂ => ‖u‖ ^ (1 / 2 : ℝ)) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards with u
  unfold motzkinSqrtOneSub
  rw [show (1 : ℂ) - (1 - u) = u by ring]
  rw [show (1 / 2 : ℂ) = (((1 / 2 : ℝ) : ℂ)) by norm_num]
  rw [Complex.norm_cpow_real u (1 / 2 : ℝ)]
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg u) _)]
  simp

lemma motzkinThird_local_residual_eq {u : ℂ} (hu1 : u ≠ 1) :
    sqrtAdjustedFun motzkinThirdAdjustedRescaledFun 3 (-motzkinAnalyticLinearCoeff) (1 - u) -
        motzkinSingularCoeff * u ^ (1 / 2 : ℂ) -
        motzkinSecondSingularCoeff * u ^ (3 / 2 : ℂ) -
        motzkinThirdSingularCoeff * u ^ (5 / 2 : ℂ) =
      (motzkinAnalyticPart (1 - u) -
        (3 + motzkinAnalyticLinearCoeff * u + motzkinAnalyticQuadraticCoeff * u ^ 2)) +
        (motzkinSingularPart (1 - u) -
          (motzkinSingularCoeff + motzkinSecondSingularCoeff * u +
            motzkinThirdSingularCoeff * u ^ 2)) *
          motzkinSqrtOneSub (1 - u) := by
  have hz_ne : (1 : ℂ) - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu1)
  have hdecomp := motzkinRescaledFun_decomp (z := 1 - u) hz_ne
  have hs : motzkinSqrtOneSub (1 - u) = u ^ (1 / 2 : ℂ) := by
    unfold motzkinSqrtOneSub
    rw [show (1 : ℂ) - (1 - u) = u by ring]
  have hpow3 : u ^ (3 / 2 : ℂ) = u * motzkinSqrtOneSub (1 - u) := by
    by_cases hu0 : u = 0
    · subst u
      norm_num [motzkinSqrtOneSub]
    · rw [hs]
      rw [show (3 / 2 : ℂ) = 1 + (1 / 2 : ℂ) by norm_num]
      rw [Complex.cpow_add _ _ hu0, Complex.cpow_one]
  have hpow5 : u ^ (5 / 2 : ℂ) = u ^ 2 * motzkinSqrtOneSub (1 - u) := by
    by_cases hu0 : u = 0
    · subst u
      norm_num [motzkinSqrtOneSub]
    · rw [hs]
      rw [show (5 / 2 : ℂ) = 2 + (1 / 2 : ℂ) by norm_num]
      rw [Complex.cpow_add _ _ hu0]
      norm_num [Complex.cpow_natCast]
  unfold sqrtAdjustedFun sqrtLinearAtOneFun motzkinThirdAdjustedRescaledFun
  rw [hdecomp, hpow3, hpow5, hs]
  ring

lemma motzkinThird_local_residual_isLittleO :
    (fun u : ℂ =>
      sqrtAdjustedFun motzkinThirdAdjustedRescaledFun 3 (-motzkinAnalyticLinearCoeff) (1 - u) -
          motzkinSingularCoeff * u ^ (1 / 2 : ℂ) -
          motzkinSecondSingularCoeff * u ^ (3 / 2 : ℂ) -
          motzkinThirdSingularCoeff * u ^ (5 / 2 : ℂ))
      =o[𝓝 (0 : ℂ)] (fun u : ℂ => ‖u‖ ^ (5 / 2 : ℝ)) := by
  have hA := motzkinAnalyticPart_remainder_isBigO.trans_isLittleO
    norm_pow_three_isLittleO_norm_rpow_five_halves
  have hBbig := motzkinSingularPart_remainder_isBigO.mul
    motzkinSqrtOneSub_local_isBigO
  have hB := hBbig.trans_isLittleO
    norm_pow_three_mul_rpow_half_isLittleO_norm_rpow_five_halves
  have hsum := hA.add hB
  refine hsum.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_ne_nhds (show (0 : ℂ) ≠ 1 by norm_num)] with u hu1
  simpa using (motzkinThird_local_residual_eq (u := u) hu1).symm

lemma tendsto_motzkinThirdAdjustedRescaledFun_singularity :
    Tendsto
      (fun z : ℂ =>
        ‖sqrtAdjustedFun motzkinThirdAdjustedRescaledFun 3 (-motzkinAnalyticLinearCoeff) z -
            motzkinSingularCoeff * (1 - z) ^ (1 / 2 : ℂ) -
            motzkinSecondSingularCoeff * (1 - z) ^ (3 / 2 : ℂ) -
            motzkinThirdSingularCoeff * (1 - z) ^ (5 / 2 : ℂ)‖ *
          ‖(1 : ℂ) - z‖ ^ (-(5 / 2 : ℝ)))
      (𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)) (𝓝 0) := by
  let l := 𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)
  have hu : Tendsto (fun z : ℂ => 1 - z) l (𝓝 (0 : ℂ)) := by
    have hcont : ContinuousAt (fun z : ℂ => 1 - z) 1 := by fun_prop
    simpa using Tendsto.mono_left hcont.tendsto nhdsWithin_le_nhds
  have hcomp := motzkinThird_local_residual_isLittleO.comp_tendsto hu
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

lemma motzkinSecondSingularCoeff_eq_meta :
    motzkinSecondSingularCoeff =
      -(((motzkinRho : ℝ) : ℂ) * motzkinSingularDerivAtRho) := by
  unfold motzkinSecondSingularCoeff motzkinRho motzkinSingularDerivAtRho
  norm_num [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_neg]
  ring

lemma motzkinThirdSingularCoeff_eq :
    motzkinThirdSingularCoeff =
      -(((1053 * Real.sqrt 3 / 128 : ℝ) : ℂ)) := by
  unfold motzkinThirdSingularCoeff motzkinRho motzkinSingularSecondDerivAtRho
  norm_num [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_neg]
  ring

lemma motzkinThirdAsymptoticConstant_eq_meta :
    sqrtSingularityC2 motzkinRho motzkinSingularCoeff
        motzkinSingularDerivAtRho motzkinSingularSecondDerivAtRho =
      ((motzkinThirdAsymptoticConstant : ℝ) : ℂ) := by
  unfold sqrtSingularityC2 sqrtSingularityC2Rescaled motzkinRho motzkinSingularCoeff
    motzkinSingularDerivAtRho motzkinSingularSecondDerivAtRho
    motzkinThirdAsymptoticConstant
  norm_num [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_neg]
  ring

lemma motzkinFirstAsymptoticConstant_eq_meta :
    sqrtSingularityC0 motzkinSingularCoeff =
      ((motzkinAsymptoticConstant : ℝ) : ℂ) := by
  unfold sqrtSingularityC0 motzkinSingularCoeff motzkinAsymptoticConstant
  norm_num [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_neg]

lemma motzkinSecondAsymptoticConstant_eq_meta :
    sqrtSingularityC1 motzkinRho motzkinSingularCoeff motzkinSingularDerivAtRho =
      ((motzkinSecondAsymptoticConstant : ℝ) : ℂ) := by
  unfold sqrtSingularityC1 sqrtSingularityC1Rescaled motzkinRho motzkinSingularCoeff
    motzkinSingularDerivAtRho motzkinSecondAsymptoticConstant
  norm_num [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_neg]
  ring

lemma motzkinSingularCoeff_ne_zero : motzkinSingularCoeff ≠ 0 := by
  unfold motzkinSingularCoeff
  norm_num

theorem motzkinThirdOriginalSeries_complex_meta :
    (fun n : ℕ =>
      PowerSeries.coeff (R := ℂ) n motzkinThirdOriginalSeriesℂ -
        (((((motzkinRho : ℝ) : ℂ)⁻¹) ^ n) *
          (sqrtSingularityC0 motzkinSingularCoeff *
              (((n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) +
            sqrtSingularityC1 motzkinRho motzkinSingularCoeff motzkinSingularDerivAtRho *
              (((n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ) +
            sqrtSingularityC2 motzkinRho motzkinSingularCoeff
                motzkinSingularDerivAtRho motzkinSingularSecondDerivAtRho *
              (((n : ℝ) ^ (-(7 / 2 : ℝ)) : ℝ) : ℂ))))
      =o[atTop]
        (fun n : ℕ =>
          ‖(((((motzkinRho : ℝ) : ℂ)⁻¹) ^ n) *
            (((n : ℝ) ^ (-(7 / 2 : ℝ)) : ℝ) : ℂ))‖) := by
  refine sqrt_singularity_thirdOrder_original_of_rescaled_singularity
    (ρ := motzkinRho) (R := (3 / 2 : ℝ)) (φ := Real.pi / 4)
    (F := motzkinThirdOriginalFun) (P := motzkinThirdOriginalSeriesℂ)
    (A0 := 3) (A1 := -motzkinAnalyticLinearCoeff)
    (Bρ := motzkinSingularCoeff)
    (Bderivρ := motzkinSingularDerivAtRho)
    (Bsecondρ := motzkinSingularSecondDerivAtRho)
    ?_ motzkinSingularCoeff_ne_zero ?_ ?_ ?_
    motzkinThirdOriginalFun_rescaled_hasFPowerSeriesAt_zero
    analyticOnNhd_motzkinThirdOriginalFun_rescaled ?_
  · unfold motzkinRho
    norm_num
  · norm_num
  · positivity
  · nlinarith [Real.pi_pos]
  · have h := tendsto_motzkinThirdAdjustedRescaledFun_singularity
    have hrescale : ∀ w : ℂ,
        motzkinThirdOriginalFun (((motzkinRho : ℝ) : ℂ) * w) =
          motzkinThirdAdjustedRescaledFun w :=
      motzkinThirdOriginalFun_rescale
    have hrescale3 : ∀ w : ℂ,
        motzkinThirdOriginalFun ((3 : ℂ)⁻¹ * w) =
          motzkinThirdAdjustedRescaledFun w := by
      intro w
      have hρ : (((motzkinRho : ℝ) : ℂ)) = (3 : ℂ)⁻¹ := by
        unfold motzkinRho
        norm_num
      rw [← hρ]
      exact hrescale w
    refine h.congr' ?_
    filter_upwards with z
    simp [sqrtAdjustedFun, hrescale, motzkinSecondSingularCoeff_eq_meta,
      motzkinThirdSingularCoeff]

lemma motzkinOneSubThreeXSeries_sq_coeff_of_three_le {n : ℕ} (hn : 3 ≤ n) :
    PowerSeries.coeff (R := ℂ) n (motzkinOneSubThreeXSeriesℂ ^ 2) = 0 := by
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
  · have hcoeff : PowerSeries.coeff (R := ℂ) i motzkinOneSubThreeXSeriesℂ = 0 := by
      unfold motzkinOneSubThreeXSeriesℂ
      simp [PowerSeries.coeff_X,
        ne_of_gt (lt_of_lt_of_le (by norm_num : 0 < 2) hi),
        ne_of_gt (lt_of_lt_of_le (by norm_num : 1 < 2) hi)]
    simp [hcoeff]
  · have hcoeff : PowerSeries.coeff (R := ℂ) j motzkinOneSubThreeXSeriesℂ = 0 := by
      unfold motzkinOneSubThreeXSeriesℂ
      simp [PowerSeries.coeff_X,
        ne_of_gt (lt_of_lt_of_le (by norm_num : 0 < 2) hj),
        ne_of_gt (lt_of_lt_of_le (by norm_num : 1 < 2) hj)]
    simp [hcoeff]

lemma coeff_motzkinThirdOriginalSeriesℂ_of_three_le {n : ℕ} (hn : 3 ≤ n) :
    PowerSeries.coeff (R := ℂ) n motzkinThirdOriginalSeriesℂ = (motzkin n : ℂ) := by
  unfold motzkinThirdOriginalSeriesℂ
  simp [PowerSeries.coeff_C_mul, motzkinOneSubThreeXSeries_sq_coeff_of_three_le hn]

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

theorem motzkin_complex_thirdOrder_additive :
    (fun n : ℕ =>
      (motzkin n : ℂ) -
        (((((3 : ℝ) ^ n) *
          (motzkinAsymptoticConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
            motzkinSecondAsymptoticConstant * (n : ℝ) ^ (-(5 / 2 : ℝ)) +
            motzkinThirdAsymptoticConstant * (n : ℝ) ^ (-(7 / 2 : ℝ))) : ℝ) : ℂ)))
      =o[atTop]
        (fun n : ℕ => (3 : ℝ) ^ n * (n : ℝ) ^ (-(7 / 2 : ℝ))) := by
  have h := motzkinThirdOriginalSeries_complex_meta
  refine h.congr' ?_ ?_
  · filter_upwards [eventually_ge_atTop 3] with n hn
    rw [coeff_motzkinThirdOriginalSeriesℂ_of_three_le hn]
    rw [motzkinFirstAsymptoticConstant_eq_meta,
      motzkinSecondAsymptoticConstant_eq_meta,
      motzkinThirdAsymptoticConstant_eq_meta]
    have hρ : (((motzkinRho : ℝ) : ℂ)⁻¹) ^ n = (((3 : ℝ) ^ n : ℝ) : ℂ) := by
      have hbase : (((motzkinRho : ℝ) : ℂ)⁻¹) = ((3 : ℝ) : ℂ) := by
        unfold motzkinRho
        norm_num
      rw [hbase, Complex.ofReal_pow]
    rw [hρ]
    norm_num [Complex.ofReal_mul, Complex.ofReal_add]
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : 0 < (n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ)) hn)
    have hρ : (((motzkinRho : ℝ) : ℂ)⁻¹) ^ n = (((3 : ℝ) ^ n : ℝ) : ℂ) := by
      have hbase : (((motzkinRho : ℝ) : ℂ)⁻¹) = ((3 : ℝ) : ℂ) := by
        unfold motzkinRho
        norm_num
      rw [hbase, Complex.ofReal_pow]
    rw [hρ, norm_mul, Complex.norm_real, Complex.norm_real]
    rw [Real.norm_of_nonneg (by positivity : 0 ≤ (3 : ℝ) ^ n)]
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (le_of_lt hnpos) _)]

theorem motzkin_thirdOrder_additive :
    (fun n : ℕ =>
      (motzkin n : ℝ) -
        (3 : ℝ) ^ n *
          (motzkinAsymptoticConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
            motzkinSecondAsymptoticConstant * (n : ℝ) ^ (-(5 / 2 : ℝ)) +
            motzkinThirdAsymptoticConstant * (n : ℝ) ^ (-(7 / 2 : ℝ))))
      =o[atTop]
        (fun n : ℕ => (3 : ℝ) ^ n * (n : ℝ) ^ (-(7 / 2 : ℝ))) := by
  have hcomplex :
      (fun n : ℕ =>
        (((motzkin n : ℝ) : ℂ) -
          ((((3 : ℝ) ^ n *
            (motzkinAsymptoticConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
              motzkinSecondAsymptoticConstant * (n : ℝ) ^ (-(5 / 2 : ℝ)) +
              motzkinThirdAsymptoticConstant * (n : ℝ) ^ (-(7 / 2 : ℝ))) : ℝ) : ℂ))))
        =o[atTop]
          (fun n : ℕ => (3 : ℝ) ^ n * (n : ℝ) ^ (-(7 / 2 : ℝ))) := by
    simpa [Complex.ofReal_mul, Complex.ofReal_add] using motzkin_complex_thirdOrder_additive
  have hreal := complex_re_isLittleO_ofReal hcomplex
  simpa using hreal

lemma motzkinThirdAsymptoticConstant_eq_relative :
    motzkinThirdAsymptoticConstant =
      motzkinAsymptoticConstant * motzkinRelativeThirdConstant := by
  unfold motzkinThirdAsymptoticConstant motzkinAsymptoticConstant
    motzkinRelativeThirdConstant
  ring

theorem motzkin_thirdOrder :
    (fun n : ℕ =>
      (motzkin n : ℝ) -
        (3 : ℝ) ^ n * motzkinAsymptoticConstant *
          (n : ℝ) ^ (-(3 / 2 : ℝ)) *
          (1 + motzkinRelativeSecondConstant * (n : ℝ) ^ (-(1 : ℝ)) +
            motzkinRelativeThirdConstant * (n : ℝ) ^ (-(2 : ℝ))))
      =o[atTop]
        (fun n : ℕ => (3 : ℝ) ^ n * (n : ℝ) ^ (-(7 / 2 : ℝ))) := by
  refine motzkin_thirdOrder_additive.congr' ?_ (EventuallyEq.refl _ _)
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
  rw [motzkinSecondAsymptoticConstant_eq_relative,
    motzkinThirdAsymptoticConstant_eq_relative, hpow5, hpow7]
  ring

lemma motzkinRelativeThirdConstant_eq_meta :
    sqrtSingularityRelativeC2 motzkinSingularCoeff
        (((motzkinRho : ℝ) : ℂ) * motzkinSingularDerivAtRho)
        ((((motzkinRho : ℝ) : ℂ) ^ 2) * motzkinSingularSecondDerivAtRho) =
      (motzkinRelativeThirdConstant : ℂ) := by
  unfold sqrtSingularityRelativeC2 motzkinRho motzkinSingularCoeff
    motzkinSingularDerivAtRho motzkinSingularSecondDerivAtRho
    motzkinRelativeThirdConstant
  norm_num [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_neg]
  have hs3 : ((Real.sqrt 3 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 3))
  field_simp [hs3]
  norm_num

end
