import AnalyticCombinatorics.Ch4.Analytic.SqrtSingularityThirdOrder
import AnalyticCombinatorics.Ch7.SingularityApp.SchroederSecondOrder

/-!
# Third-order large Schroeder asymptotics

This file plugs the large-Schroeder square-root data at
`ρ = 3 - 2 * sqrt 2` into the third-order square-root applicator.
-/

set_option maxHeartbeats 1200000

open Complex Filter Asymptotics Set
open scoped Topology BigOperators PowerSeries

noncomputable section

def schroederAnalyticQuadraticCoeff : ℂ :=
  2 / schroederOneSubRhoℂ ^ 2

def schroederSqrtRegularLinearCoeff : ℂ :=
  schroederRhoℂ ^ 2 / (2 * schroederSqrtRegularAtOneℂ)

def schroederSqrtRegularQuadraticCoeff : ℂ :=
  -(schroederRhoℂ ^ 4) / (8 * schroederSqrtRegularAtOneℂ ^ 3)

def schroederThirdKℂ : ℂ :=
  schroederSqrtRegularAtOneℂ + schroederSqrtRegularLinearCoeff +
    schroederSqrtRegularQuadraticCoeff

def schroederThirdSingularCoeff : ℂ :=
  -2 * schroederThirdKℂ / schroederOneSubRhoℂ ^ 2

def schroederSingularDerivAtRho : ℂ :=
  -schroederSecondSingularCoeff / schroederRhoℂ

def schroederSingularSecondDerivAtRho : ℂ :=
  2 * schroederThirdSingularCoeff / schroederRhoℂ ^ 2

private lemma schroederSqrtRegularAtOne_add_self_ne_zero :
    schroederSqrtRegularAtOneℂ + schroederSqrtRegularAtOneℂ ≠ 0 := by
  intro h
  have hmul : (2 : ℂ) * schroederSqrtRegularAtOneℂ = 0 := by
    simpa [two_mul] using h
  rcases mul_eq_zero.mp hmul with htwo | ht
  · norm_num at htwo
  · exact schroederSqrtRegularAtOne_ne_zero ht

private lemma schroederOneSubRhoℂ_ne_zero : schroederOneSubRhoℂ ≠ 0 := by
  unfold schroederOneSubRhoℂ
  exact one_sub_schroederRho_ne_zeroℂ

def schroederThirdOriginalOneSubSeriesℂ : PowerSeries ℂ :=
  (1 : PowerSeries ℂ) - PowerSeries.C schroederRhoℂ⁻¹ * PowerSeries.X

def schroederThirdOriginalSeriesℂ : PowerSeries ℂ :=
  schroederSeriesℂ -
    PowerSeries.C schroederAnalyticQuadraticCoeff *
      schroederThirdOriginalOneSubSeriesℂ ^ 2

def schroederThirdAdjustedRescaledSeriesℂ : PowerSeries ℂ :=
  schroederRescaledSeriesℂ -
    PowerSeries.C schroederAnalyticQuadraticCoeff * schroederOneSubSeriesℂ ^ 2

def schroederThirdOriginalFun (z : ℂ) : ℂ :=
  schroederRescaledFun (schroederRhoℂ⁻¹ * z) -
    schroederAnalyticQuadraticCoeff * (1 - schroederRhoℂ⁻¹ * z) ^ 2

def schroederThirdAdjustedRescaledFun (z : ℂ) : ℂ :=
  schroederRescaledFun z - schroederAnalyticQuadraticCoeff * (1 - z) ^ 2

lemma schroederThirdOriginalFun_rescale (z : ℂ) :
    schroederThirdOriginalFun (schroederRhoℂ * z) =
      schroederThirdAdjustedRescaledFun z := by
  have hρ : schroederRhoℂ ≠ 0 := by
    unfold schroederRhoℂ
    exact_mod_cast schroederRho_ne_zero
  unfold schroederThirdOriginalFun schroederThirdAdjustedRescaledFun
  have hscale : schroederRhoℂ⁻¹ * (schroederRhoℂ * z) = z := by
    rw [← mul_assoc, inv_mul_cancel₀ hρ, one_mul]
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

lemma rescale_schroederThirdOriginalOneSubSeriesℂ :
    PowerSeries.rescale schroederRhoℂ schroederThirdOriginalOneSubSeriesℂ =
      schroederOneSubSeriesℂ := by
  have hρ : schroederRhoℂ ≠ 0 := by
    unfold schroederRhoℂ
    exact_mod_cast schroederRho_ne_zero
  ext n
  rw [PowerSeries.coeff_rescale]
  cases n with
  | zero =>
      simp [schroederThirdOriginalOneSubSeriesℂ, schroederOneSubSeriesℂ]
  | succ n =>
      cases n with
      | zero =>
          simp [schroederThirdOriginalOneSubSeriesℂ, schroederOneSubSeriesℂ,
            PowerSeries.coeff_X, PowerSeries.coeff_C, hρ]
      | succ n =>
          simp [schroederThirdOriginalOneSubSeriesℂ, schroederOneSubSeriesℂ,
            PowerSeries.coeff_X]

lemma rescale_schroederThirdOriginalSeriesℂ :
    PowerSeries.rescale schroederRhoℂ schroederThirdOriginalSeriesℂ =
      schroederThirdAdjustedRescaledSeriesℂ := by
  unfold schroederThirdOriginalSeriesℂ schroederThirdAdjustedRescaledSeriesℂ
  simp only [map_sub, map_mul, map_pow, rescale_schroederThirdOriginalOneSubSeriesℂ]
  rw [PowerSeries_rescale_C]
  rfl

lemma schroederThirdAdjustedRescaledFun_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt schroederThirdAdjustedRescaledFun
      (PowerSeries.toFMLS schroederThirdAdjustedRescaledSeriesℂ) (0 : ℂ) := by
  have hsquare : HasFPowerSeriesAt (fun z : ℂ => (1 - z) * (1 - z))
      (PowerSeries.toFMLS (schroederOneSubSeriesℂ ^ 2)) (0 : ℂ) := by
    simpa [pow_two] using
      hasFPowerSeriesAt_mul_toFMLS hasFPowerSeriesAt_schroederOneSub_toFMLS
        hasFPowerSeriesAt_schroederOneSub_toFMLS
  have hquad : HasFPowerSeriesAt
      (fun z : ℂ => schroederAnalyticQuadraticCoeff * (1 - z) ^ 2)
      (PowerSeries.toFMLS
        (PowerSeries.C schroederAnalyticQuadraticCoeff *
          schroederOneSubSeriesℂ ^ 2)) (0 : ℂ) := by
    have h := hsquare.const_smul (c := schroederAnalyticQuadraticCoeff)
    convert h using 1
    · ext z
      simp [pow_two, smul_eq_mul]
    · ext n
      simp [PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars,
        PowerSeries.coeff_C_mul]
  have hsub := schroederRescaledFun_hasFPowerSeriesAt_zero.sub hquad
  simpa [schroederThirdAdjustedRescaledFun, schroederThirdAdjustedRescaledSeriesℂ,
    toFMLS_sub] using hsub

lemma schroederThirdOriginalFun_rescaled_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt
      (fun z : ℂ => schroederThirdOriginalFun (schroederRhoℂ * z))
      (PowerSeries.toFMLS
        (PowerSeries.rescale schroederRhoℂ schroederThirdOriginalSeriesℂ))
      (0 : ℂ) := by
  rw [rescale_schroederThirdOriginalSeriesℂ]
  simpa [schroederThirdOriginalFun_rescale] using
    schroederThirdAdjustedRescaledFun_hasFPowerSeriesAt_zero

lemma analyticOnNhd_schroederThirdAdjustedRescaledFun :
    AnalyticOnNhd ℂ schroederThirdAdjustedRescaledFun
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
  have hquad : AnalyticOnNhd ℂ
      (fun z : ℂ => schroederAnalyticQuadraticCoeff * (1 - z) ^ 2)
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
    simpa [pow_two] using
      (analyticOnNhd_const.mul
        ((analyticOnNhd_const.sub analyticOnNhd_id).mul
          (analyticOnNhd_const.sub analyticOnNhd_id)))
  simpa [schroederThirdAdjustedRescaledFun] using
    analyticOnNhd_schroederRescaledFun.sub hquad

lemma analyticOnNhd_schroederThirdOriginalFun_rescaled :
    AnalyticOnNhd ℂ
      (fun z : ℂ => schroederThirdOriginalFun (schroederRhoℂ * z))
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
  simpa [schroederThirdOriginalFun_rescale] using
    analyticOnNhd_schroederThirdAdjustedRescaledFun

def schroederAnalyticPart (z : ℂ) : ℂ :=
  2 * (1 - schroederRhoℂ * z) / (schroederOneSubRhoℂ ^ 2 * z)

def schroederSingularPart (z : ℂ) : ℂ :=
  -2 * schroederSqrtRegular z / (schroederOneSubRhoℂ ^ 2 * z)

lemma schroederRescaledFun_decomp {z : ℂ} (hz : z ≠ 0) :
    schroederRescaledFun z =
      schroederAnalyticPart z + schroederSingularPart z * schroederSqrtOneSub z := by
  unfold schroederRescaledFun schroederAnalyticPart schroederSingularPart
  rw [div_eq_iff (schroederRescaledDenominator_ne_zero z)]
  have hzq : schroederOneSubRhoℂ ^ 2 * z ≠ 0 := by
    exact mul_ne_zero (pow_ne_zero 2 one_sub_schroederRho_ne_zeroℂ) hz
  have hden := schroederRescaledDenominator_ne_zero z
  field_simp [hzq, hden]
  unfold schroederRescaledDenominator
  ring_nf
  rw [schroederSqrtRegular_sq, schroederSqrtOneSub_sq]
  rw [schroederOneSubRhoℂ_eq]
  have hq : (1 : ℂ) - schroederRhoℂ ≠ 0 := by
    simpa [schroederOneSubRhoℂ, schroederRhoℂ, Complex.ofReal_sub] using
      one_sub_schroederRho_ne_zeroℂ
  field_simp [pow_ne_zero 2 hq]
  ring

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

def schroederSqrtRegularTaylor (u : ℂ) : ℂ :=
  schroederSqrtRegularAtOneℂ +
    schroederSqrtRegularLinearCoeff * u +
      schroederSqrtRegularQuadraticCoeff * u ^ 2

def schroederSqrtRegularBTaylor (u : ℂ) : ℂ :=
  -(schroederOneSubRhoℂ ^ 2 / 2) *
    (schroederSingularCoeff + schroederSecondSingularCoeff * u +
      schroederThirdSingularCoeff * u ^ 2) * (1 - u)

lemma schroederSqrtRegular_sq_sub_taylor_sq (u : ℂ) :
    (schroederSqrtRegular (1 - u)) ^ 2 -
        (schroederSqrtRegularTaylor u) ^ 2 =
      u ^ 3 *
        (schroederRhoℂ ^ 6 / (8 * schroederSqrtRegularAtOneℂ ^ 4) -
          schroederRhoℂ ^ 8 / (64 * schroederSqrtRegularAtOneℂ ^ 6) * u) := by
  unfold schroederSqrtRegularTaylor schroederSqrtRegularLinearCoeff
    schroederSqrtRegularQuadraticCoeff
  rw [schroederSqrtRegular_sq]
  field_simp [schroederSqrtRegularAtOne_ne_zero]
  rw [show schroederSqrtRegularAtOneℂ ^ 6 =
      (1 - schroederRhoℂ ^ 2) ^ 3 by
        rw [show schroederSqrtRegularAtOneℂ ^ 6 =
            (schroederSqrtRegularAtOneℂ ^ 2) ^ 3 by ring,
          schroederSqrtRegularAtOne_sq]]
  rw [schroederSqrtRegularAtOne_sq]
  ring

lemma schroederSqrtRegular_sub_taylor_isBigO :
    (fun u : ℂ => schroederSqrtRegular (1 - u) - schroederSqrtRegularTaylor u)
      =O[𝓝 (0 : ℂ)] (fun u : ℂ => ‖u‖ ^ 3) := by
  let t : ℂ → ℂ := fun u => schroederSqrtRegular (1 - u)
  let q : ℂ → ℂ := schroederSqrtRegularTaylor
  have ht : Tendsto t (𝓝 (0 : ℂ)) (𝓝 schroederSqrtRegularAtOneℂ) := by
    have harg : Tendsto (fun u : ℂ => 1 - u) (𝓝 (0 : ℂ)) (𝓝 (1 : ℂ)) := by
      simpa using
        (continuousAt_const.sub continuousAt_id : ContinuousAt (fun u : ℂ => 1 - u) 0).tendsto
    have h := hasDerivAt_schroederSqrtRegular_one.continuousAt.tendsto.comp harg
    simpa [t, schroederSqrtRegular_one] using h
  have hq : Tendsto q (𝓝 (0 : ℂ)) (𝓝 schroederSqrtRegularAtOneℂ) := by
    have hcont : ContinuousAt q 0 := by
      unfold q schroederSqrtRegularTaylor
      fun_prop
    simpa [q, schroederSqrtRegularTaylor] using hcont.tendsto
  have hden : Tendsto (fun u : ℂ => (t u + q u)⁻¹) (𝓝 (0 : ℂ))
      (𝓝 ((schroederSqrtRegularAtOneℂ + schroederSqrtRegularAtOneℂ)⁻¹)) := by
    exact (ht.add hq).inv₀ schroederSqrtRegularAtOne_add_self_ne_zero
  have hdenO : (fun u : ℂ => (t u + q u)⁻¹) =O[𝓝 (0 : ℂ)]
      (fun _ : ℂ => (1 : ℝ)) :=
    tendsto_isBigO_one_complex hden
  have hsqO : (fun u : ℂ => (t u) ^ 2 - (q u) ^ 2) =O[𝓝 (0 : ℂ)]
      (fun u : ℂ => ‖u‖ ^ 3) := by
    have hbase := cubic_mul_continuous_isBigO
      (fun u : ℂ =>
        schroederRhoℂ ^ 6 / (8 * schroederSqrtRegularAtOneℂ ^ 4) -
          schroederRhoℂ ^ 8 / (64 * schroederSqrtRegularAtOneℂ ^ 6) * u)
      (by fun_prop)
    refine hbase.congr_left ?_
    intro u
    dsimp [t, q]
    rw [schroederSqrtRegular_sq_sub_taylor_sq]
  have hprod := hsqO.mul hdenO
  refine hprod.congr' ?_ ?_
  · have hsum_ne : ∀ᶠ u : ℂ in 𝓝 (0 : ℂ), t u + q u ≠ 0 := by
      have hsum := ht.add hq
      exact hsum.eventually_ne schroederSqrtRegularAtOne_add_self_ne_zero
    filter_upwards [hsum_ne] with u hu
    dsimp [t, q] at hu ⊢
    set a := schroederSqrtRegular (1 - u)
    set b := schroederSqrtRegularTaylor u
    rw [show a ^ 2 - b ^ 2 = (a - b) * (a + b) by ring]
    rw [mul_assoc, mul_inv_cancel₀ hu, mul_one]
  · filter_upwards with u
    ring

lemma schroederAnalyticPart_remainder_isBigO :
    (fun u : ℂ =>
      schroederAnalyticPart (1 - u) -
        (schroederRegularValueℂ + schroederAnalyticLinearCoeff * u +
          schroederAnalyticQuadraticCoeff * u ^ 2))
      =O[𝓝 (0 : ℂ)] (fun u : ℂ => ‖u‖ ^ 3) := by
  have hbase := cubic_mul_continuous_isBigO
    (fun u : ℂ => (2 / schroederOneSubRhoℂ ^ 2) / (1 - u))
    (by
      apply ContinuousAt.div
      · fun_prop
      · fun_prop
      · norm_num)
  refine hbase.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_ne_nhds (show (0 : ℂ) ≠ 1 by norm_num)] with u hu
  unfold schroederAnalyticPart schroederRegularValueℂ schroederAnalyticLinearCoeff
    schroederAnalyticQuadraticCoeff
  rw [schroederOneSubRhoℂ_eq]
  have hq : (1 : ℂ) - schroederRhoℂ ≠ 0 := by
    simpa [schroederOneSubRhoℂ, schroederRhoℂ, Complex.ofReal_sub] using
      one_sub_schroederRho_ne_zeroℂ
  field_simp [sub_ne_zero.mpr (Ne.symm hu), hq, pow_ne_zero 2 hq]
  ring

lemma schroederSqrtRegularTaylor_sub_BTaylor_isBigO :
    (fun u : ℂ => schroederSqrtRegularTaylor u - schroederSqrtRegularBTaylor u)
      =O[𝓝 (0 : ℂ)] (fun u : ℂ => ‖u‖ ^ 3) := by
  have hbase := cubic_mul_continuous_isBigO
    (fun _u : ℂ =>
      schroederSqrtRegularAtOneℂ + schroederSqrtRegularLinearCoeff +
        schroederSqrtRegularQuadraticCoeff)
    (by fun_prop)
  refine hbase.congr_left ?_
  intro u
  dsimp
  unfold schroederSqrtRegularTaylor schroederSqrtRegularBTaylor
    schroederThirdSingularCoeff schroederSecondSingularCoeff
    schroederSecondKℂ schroederSingularCoeff schroederSqrtRegularLinearCoeff
    schroederSqrtRegularQuadraticCoeff
  unfold schroederThirdKℂ
  unfold schroederSqrtRegularLinearCoeff schroederSqrtRegularQuadraticCoeff
  field_simp [schroederSqrtRegularAtOne_ne_zero,
    schroederOneSubRhoℂ_ne_zero, pow_ne_zero 2 schroederOneSubRhoℂ_ne_zero]
  field_simp [schroederOneSubRhoℂ_ne_zero]
  rw [show schroederSqrtRegularAtOneℂ ^ 2 = 1 - schroederRhoℂ ^ 2 by
    exact schroederSqrtRegularAtOne_sq]
  field_simp [one_sub_schroederRho_ne_zeroℂ]
  try ring_nf

lemma schroederSingularPart_remainder_isBigO :
    (fun u : ℂ =>
      schroederSingularPart (1 - u) -
        (schroederSingularCoeff + schroederSecondSingularCoeff * u +
          schroederThirdSingularCoeff * u ^ 2))
      =O[𝓝 (0 : ℂ)] (fun u : ℂ => ‖u‖ ^ 3) := by
  have hdiff : (fun u : ℂ =>
      schroederSqrtRegular (1 - u) - schroederSqrtRegularBTaylor u)
      =O[𝓝 (0 : ℂ)] (fun u : ℂ => ‖u‖ ^ 3) := by
    have hsum := schroederSqrtRegular_sub_taylor_isBigO.add
      schroederSqrtRegularTaylor_sub_BTaylor_isBigO
    refine hsum.congr_left ?_
    intro u
    ring
  have hden_tendsto : Tendsto (fun u : ℂ => (1 - u)⁻¹) (𝓝 (0 : ℂ))
      (𝓝 (1 : ℂ)) := by
    have hcont : ContinuousAt (fun u : ℂ => 1 - u) 0 := by fun_prop
    have hne : (1 - (0 : ℂ)) ≠ 0 := by norm_num
    convert hcont.tendsto.inv₀ hne using 1
    norm_num
  have hdenO : (fun u : ℂ => (1 - u)⁻¹) =O[𝓝 (0 : ℂ)]
      (fun _ : ℂ => (1 : ℝ)) :=
    tendsto_isBigO_one_complex hden_tendsto
  have hprod := hdiff.mul hdenO
  have hscaled : (fun u : ℂ =>
      (-2 / schroederOneSubRhoℂ ^ 2) *
        ((schroederSqrtRegular (1 - u) - schroederSqrtRegularBTaylor u) *
          (1 - u)⁻¹))
      =O[𝓝 (0 : ℂ)] (fun u : ℂ => ‖u‖ ^ 3) := by
    refine (hprod.const_mul_left (-2 / schroederOneSubRhoℂ ^ 2)).congr_right ?_
    intro u
    ring
  refine hscaled.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_ne_nhds (show (0 : ℂ) ≠ 1 by norm_num)] with u hu
  unfold schroederSingularPart schroederSqrtRegularBTaylor
  field_simp [sub_ne_zero.mpr (Ne.symm hu), schroederOneSubRhoℂ_ne_zero,
    pow_ne_zero 2 schroederOneSubRhoℂ_ne_zero]
  field_simp [schroederOneSubRhoℂ_ne_zero]
  try ring

lemma schroederSqrtOneSub_local_isBigO :
    (fun u : ℂ => schroederSqrtOneSub (1 - u)) =O[𝓝 (0 : ℂ)]
      (fun u : ℂ => ‖u‖ ^ (1 / 2 : ℝ)) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards with u
  unfold schroederSqrtOneSub
  rw [show (1 : ℂ) - (1 - u) = u by ring]
  rw [show (1 / 2 : ℂ) = (((1 / 2 : ℝ) : ℂ)) by norm_num]
  rw [Complex.norm_cpow_real u (1 / 2 : ℝ)]
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg u) _)]
  simp

lemma schroederThird_local_residual_eq {u : ℂ} (hu1 : u ≠ 1) :
    sqrtAdjustedFun schroederThirdAdjustedRescaledFun schroederRegularValueℂ
        (-schroederAnalyticLinearCoeff) (1 - u) -
        schroederSingularCoeff * u ^ (1 / 2 : ℂ) -
        schroederSecondSingularCoeff * u ^ (3 / 2 : ℂ) -
        schroederThirdSingularCoeff * u ^ (5 / 2 : ℂ) =
      (schroederAnalyticPart (1 - u) -
        (schroederRegularValueℂ + schroederAnalyticLinearCoeff * u +
          schroederAnalyticQuadraticCoeff * u ^ 2)) +
        (schroederSingularPart (1 - u) -
          (schroederSingularCoeff + schroederSecondSingularCoeff * u +
            schroederThirdSingularCoeff * u ^ 2)) *
          schroederSqrtOneSub (1 - u) := by
  have hz_ne : (1 : ℂ) - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu1)
  have hdecomp := schroederRescaledFun_decomp (z := 1 - u) hz_ne
  have hs : schroederSqrtOneSub (1 - u) = u ^ (1 / 2 : ℂ) := by
    unfold schroederSqrtOneSub
    rw [show (1 : ℂ) - (1 - u) = u by ring]
  have hpow3 : u ^ (3 / 2 : ℂ) = u * schroederSqrtOneSub (1 - u) := by
    by_cases hu0 : u = 0
    · subst u
      norm_num [schroederSqrtOneSub]
    · rw [hs]
      rw [show (3 / 2 : ℂ) = 1 + (1 / 2 : ℂ) by norm_num]
      rw [Complex.cpow_add _ _ hu0, Complex.cpow_one]
  have hpow5 : u ^ (5 / 2 : ℂ) = u ^ 2 * schroederSqrtOneSub (1 - u) := by
    by_cases hu0 : u = 0
    · subst u
      norm_num [schroederSqrtOneSub]
    · rw [hs]
      rw [show (5 / 2 : ℂ) = 2 + (1 / 2 : ℂ) by norm_num]
      rw [Complex.cpow_add _ _ hu0]
      norm_num [Complex.cpow_natCast]
  unfold sqrtAdjustedFun sqrtLinearAtOneFun schroederThirdAdjustedRescaledFun
  rw [hdecomp, hpow3, hpow5, hs]
  ring

lemma schroederThird_local_residual_isLittleO :
    (fun u : ℂ =>
      sqrtAdjustedFun schroederThirdAdjustedRescaledFun schroederRegularValueℂ
          (-schroederAnalyticLinearCoeff) (1 - u) -
          schroederSingularCoeff * u ^ (1 / 2 : ℂ) -
          schroederSecondSingularCoeff * u ^ (3 / 2 : ℂ) -
          schroederThirdSingularCoeff * u ^ (5 / 2 : ℂ))
      =o[𝓝 (0 : ℂ)] (fun u : ℂ => ‖u‖ ^ (5 / 2 : ℝ)) := by
  have hA := schroederAnalyticPart_remainder_isBigO.trans_isLittleO
    norm_pow_three_isLittleO_norm_rpow_five_halves
  have hBbig := schroederSingularPart_remainder_isBigO.mul
    schroederSqrtOneSub_local_isBigO
  have hB := hBbig.trans_isLittleO
    norm_pow_three_mul_rpow_half_isLittleO_norm_rpow_five_halves
  have hsum := hA.add hB
  refine hsum.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_ne_nhds (show (0 : ℂ) ≠ 1 by norm_num)] with u hu1
  simpa using (schroederThird_local_residual_eq (u := u) hu1).symm

lemma tendsto_schroederThirdAdjustedRescaledFun_singularity :
    Tendsto
      (fun z : ℂ =>
        ‖sqrtAdjustedFun schroederThirdAdjustedRescaledFun schroederRegularValueℂ
            (-schroederAnalyticLinearCoeff) z -
            schroederSingularCoeff * (1 - z) ^ (1 / 2 : ℂ) -
            schroederSecondSingularCoeff * (1 - z) ^ (3 / 2 : ℂ) -
            schroederThirdSingularCoeff * (1 - z) ^ (5 / 2 : ℂ)‖ *
          ‖(1 : ℂ) - z‖ ^ (-(5 / 2 : ℝ)))
      (𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)) (𝓝 0) := by
  let l := 𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)
  have hu : Tendsto (fun z : ℂ => 1 - z) l (𝓝 (0 : ℂ)) := by
    have hcont : ContinuousAt (fun z : ℂ => 1 - z) 1 := by fun_prop
    simpa using Tendsto.mono_left hcont.tendsto nhdsWithin_le_nhds
  have hcomp := schroederThird_local_residual_isLittleO.comp_tendsto hu
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

lemma schroederSecondSingularCoeff_eq_meta :
    schroederSecondSingularCoeff =
      -(schroederRhoℂ * schroederSingularDerivAtRho) := by
  unfold schroederSingularDerivAtRho
  field_simp [show schroederRhoℂ ≠ 0 by
    unfold schroederRhoℂ
    exact_mod_cast schroederRho_ne_zero]

lemma schroederThirdSingularCoeff_eq_meta :
    schroederThirdSingularCoeff =
      (schroederRhoℂ ^ 2 * schroederSingularSecondDerivAtRho) / 2 := by
  unfold schroederSingularSecondDerivAtRho
  field_simp [show schroederRhoℂ ≠ 0 by
    unfold schroederRhoℂ
    exact_mod_cast schroederRho_ne_zero]

lemma schroederSingularCoeff_ne_zero : schroederSingularCoeff ≠ 0 := by
  unfold schroederSingularCoeff
  exact div_ne_zero
    (mul_ne_zero (by norm_num) schroederSqrtRegularAtOne_ne_zero)
    (pow_ne_zero 2 one_sub_schroederRho_ne_zeroℂ)

theorem schroederThirdOriginalSeries_complex_meta :
    (fun n : ℕ =>
      PowerSeries.coeff (R := ℂ) n schroederThirdOriginalSeriesℂ -
        (((schroederRhoℂ⁻¹) ^ n) *
          (sqrtSingularityC0 schroederSingularCoeff *
              (((n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) +
            sqrtSingularityC1 schroederRho schroederSingularCoeff
                schroederSingularDerivAtRho *
              (((n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ) +
            sqrtSingularityC2 schroederRho schroederSingularCoeff
                schroederSingularDerivAtRho schroederSingularSecondDerivAtRho *
              (((n : ℝ) ^ (-(7 / 2 : ℝ)) : ℝ) : ℂ))))
      =o[atTop]
        (fun n : ℕ =>
          ‖((schroederRhoℂ⁻¹) ^ n *
            (((n : ℝ) ^ (-(7 / 2 : ℝ)) : ℝ) : ℂ))‖) := by
  refine sqrt_singularity_thirdOrder_original_of_rescaled_singularity
    (ρ := schroederRho) (R := (3 / 2 : ℝ)) (φ := Real.pi / 4)
    (F := schroederThirdOriginalFun) (P := schroederThirdOriginalSeriesℂ)
    (A0 := schroederRegularValueℂ) (A1 := -schroederAnalyticLinearCoeff)
    (Bρ := schroederSingularCoeff)
    (Bderivρ := schroederSingularDerivAtRho)
    (Bsecondρ := schroederSingularSecondDerivAtRho)
    schroederRho_pos schroederSingularCoeff_ne_zero ?_ ?_ ?_
    ?_ ?_ ?_
  · norm_num
  · positivity
  · nlinarith [Real.pi_pos]
  · simpa [schroederRhoℂ] using
      schroederThirdOriginalFun_rescaled_hasFPowerSeriesAt_zero
  · simpa [schroederRhoℂ] using
      analyticOnNhd_schroederThirdOriginalFun_rescaled
  · have h := tendsto_schroederThirdAdjustedRescaledFun_singularity
    refine h.congr' ?_
    filter_upwards with z
    have hfun :
        schroederThirdOriginalFun (((schroederRho : ℝ) : ℂ) * z) =
          schroederThirdAdjustedRescaledFun z := by
      change schroederThirdOriginalFun (schroederRhoℂ * z) =
        schroederThirdAdjustedRescaledFun z
      exact schroederThirdOriginalFun_rescale z
    have hadj :
        sqrtAdjustedFun
            (fun w : ℂ => schroederThirdOriginalFun (((schroederRho : ℝ) : ℂ) * w))
            schroederRegularValueℂ (-schroederAnalyticLinearCoeff) z =
          sqrtAdjustedFun schroederThirdAdjustedRescaledFun schroederRegularValueℂ
            (-schroederAnalyticLinearCoeff) z := by
      unfold sqrtAdjustedFun
      simpa using
        congrArg (fun x : ℂ =>
          x - sqrtLinearAtOneFun schroederRegularValueℂ
            (-schroederAnalyticLinearCoeff) z) hfun
    rw [hadj]
    rw [show -(((schroederRho : ℝ) : ℂ) * schroederSingularDerivAtRho) =
        schroederSecondSingularCoeff by
          change -(schroederRhoℂ * schroederSingularDerivAtRho) =
            schroederSecondSingularCoeff
          exact schroederSecondSingularCoeff_eq_meta.symm]
    rw [show ((((schroederRho : ℝ) : ℂ) ^ 2 *
          schroederSingularSecondDerivAtRho) / 2) =
        schroederThirdSingularCoeff by
          change (schroederRhoℂ ^ 2 * schroederSingularSecondDerivAtRho) / 2 =
            schroederThirdSingularCoeff
          exact schroederThirdSingularCoeff_eq_meta.symm]

lemma schroederThirdOriginalOneSubSeries_sq_coeff_of_three_le {n : ℕ} (hn : 3 ≤ n) :
    PowerSeries.coeff (R := ℂ) n (schroederThirdOriginalOneSubSeriesℂ ^ 2) = 0 := by
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
  · have hcoeff : PowerSeries.coeff (R := ℂ) i schroederThirdOriginalOneSubSeriesℂ = 0 := by
      unfold schroederThirdOriginalOneSubSeriesℂ
      simp [PowerSeries.coeff_X,
        ne_of_gt (lt_of_lt_of_le (by norm_num : 0 < 2) hi),
        ne_of_gt (lt_of_lt_of_le (by norm_num : 1 < 2) hi)]
    simp [hcoeff]
  · have hcoeff : PowerSeries.coeff (R := ℂ) j schroederThirdOriginalOneSubSeriesℂ = 0 := by
      unfold schroederThirdOriginalOneSubSeriesℂ
      simp [PowerSeries.coeff_X,
        ne_of_gt (lt_of_lt_of_le (by norm_num : 0 < 2) hj),
        ne_of_gt (lt_of_lt_of_le (by norm_num : 1 < 2) hj)]
    simp [hcoeff]

lemma coeff_schroederThirdOriginalSeriesℂ_of_three_le {n : ℕ} (hn : 3 ≤ n) :
    PowerSeries.coeff (R := ℂ) n schroederThirdOriginalSeriesℂ = (schroeder n : ℂ) := by
  unfold schroederThirdOriginalSeriesℂ
  simp [PowerSeries.coeff_C_mul, schroederThirdOriginalOneSubSeries_sq_coeff_of_three_le hn]

def schroederThirdLeadingConstantℂ : ℂ :=
  sqrtSingularityC0 schroederSingularCoeff

def schroederRelativeSecondMetaConstantℂ : ℂ :=
  sqrtSingularityC1 schroederRho schroederSingularCoeff schroederSingularDerivAtRho /
    schroederThirdLeadingConstantℂ

def schroederRelativeThirdMetaConstantℂ : ℂ :=
  sqrtSingularityC2 schroederRho schroederSingularCoeff schroederSingularDerivAtRho
      schroederSingularSecondDerivAtRho /
    schroederThirdLeadingConstantℂ

lemma schroederThirdLeadingConstantℂ_ne_zero :
    schroederThirdLeadingConstantℂ ≠ 0 := by
  unfold schroederThirdLeadingConstantℂ sqrtSingularityC0
  have hden : (((2 * Real.sqrt Real.pi : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast
      (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0)
        (Real.sqrt_ne_zero'.mpr Real.pi_pos))
  exact div_ne_zero (neg_ne_zero.mpr schroederSingularCoeff_ne_zero) hden

theorem schroeder_complex_thirdOrder_additive_meta :
    (fun n : ℕ =>
      (schroeder n : ℂ) -
        ((schroederRhoℂ⁻¹) ^ n *
          (sqrtSingularityC0 schroederSingularCoeff *
              (((n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) +
            sqrtSingularityC1 schroederRho schroederSingularCoeff
                schroederSingularDerivAtRho *
              (((n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ) +
            sqrtSingularityC2 schroederRho schroederSingularCoeff
                schroederSingularDerivAtRho schroederSingularSecondDerivAtRho *
              (((n : ℝ) ^ (-(7 / 2 : ℝ)) : ℝ) : ℂ))))
      =o[atTop]
        (fun n : ℕ =>
          ‖((schroederRhoℂ⁻¹) ^ n *
            (((n : ℝ) ^ (-(7 / 2 : ℝ)) : ℝ) : ℂ))‖) := by
  have h := schroederThirdOriginalSeries_complex_meta
  refine h.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_ge_atTop 3] with n hn
  rw [coeff_schroederThirdOriginalSeriesℂ_of_three_le hn]

theorem schroeder_complex_thirdOrder :
    (fun n : ℕ =>
      (schroeder n : ℂ) -
        (schroederRhoℂ⁻¹) ^ n * schroederThirdLeadingConstantℂ *
          (((n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
          (1 + schroederRelativeSecondMetaConstantℂ *
              (((n : ℝ) ^ (-(1 : ℝ)) : ℝ) : ℂ) +
            schroederRelativeThirdMetaConstantℂ *
              (((n : ℝ) ^ (-(2 : ℝ)) : ℝ) : ℂ)))
      =o[atTop]
        (fun n : ℕ =>
          ‖((schroederRhoℂ⁻¹) ^ n *
            (((n : ℝ) ^ (-(7 / 2 : ℝ)) : ℝ) : ℂ))‖) := by
  refine schroeder_complex_thirdOrder_additive_meta.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ)) hn)
  have hpow5 :
      (((n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ) =
        (((n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
          (((n : ℝ) ^ (-(1 : ℝ)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    rw [← Real.rpow_add hnpos]
    norm_num
  have hpow7 :
      (((n : ℝ) ^ (-(7 / 2 : ℝ)) : ℝ) : ℂ) =
        (((n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
          (((n : ℝ) ^ (-(2 : ℝ)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    rw [← Real.rpow_add hnpos]
    norm_num
  unfold schroederRelativeSecondMetaConstantℂ schroederRelativeThirdMetaConstantℂ
  rw [hpow5, hpow7]
  field_simp [schroederThirdLeadingConstantℂ_ne_zero]
  unfold schroederThirdLeadingConstantℂ
  ring
