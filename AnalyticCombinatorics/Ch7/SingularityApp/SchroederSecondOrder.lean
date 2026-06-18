import AnalyticCombinatorics.Ch4.Analytic.TransferSecondOrderGeneral
import AnalyticCombinatorics.Ch7.SingularityApp.Schroeder

/-!
# Second-order large Schroeder asymptotics

This file subtracts the analytic linear term in the centered rescaled
Schroeder OGF and applies `transfer_twoTerm_secondOrder_general` at
`α = -1/2`.
-/

set_option maxHeartbeats 1200000

open Complex Filter Asymptotics Set
open scoped Topology BigOperators PowerSeries

noncomputable section

def schroederAnalyticLinearCoeff : ℂ :=
  2 / schroederOneSubRhoℂ ^ 2

def schroederSecondKℂ : ℂ :=
  (2 - schroederRhoℂ ^ 2) / schroederSqrtRegularAtOneℂ

def schroederSecondSingularCoeff : ℂ :=
  -schroederSecondKℂ / schroederOneSubRhoℂ ^ 2

def schroederSecondSingularRatio : ℝ :=
  3 / 4 + 3 * Real.sqrt 2 / 16

def schroederRelativeSecondConstant : ℝ :=
  -3 / 4 - 9 * Real.sqrt 2 / 32

def schroederSecondAsymptoticConstant : ℝ :=
  schroederAsymptoticConstant * schroederRelativeSecondConstant

def schroederOneSubSeriesℂ : PowerSeries ℂ :=
  (1 : PowerSeries ℂ) - PowerSeries.X

def schroederAdjustedRescaledFMLS : FormalMultilinearSeries ℂ ℂ ℂ :=
  PowerSeries.toFMLS schroederCenteredRescaledSeriesℂ -
    schroederAnalyticLinearCoeff • PowerSeries.toFMLS schroederOneSubSeriesℂ

def schroederAdjustedRescaledFun (z : ℂ) : ℂ :=
  schroederCenteredRescaledFun z - schroederAnalyticLinearCoeff * (1 - z)

private lemma coeff_sub_const_smul (C : ℂ)
    (p q : FormalMultilinearSeries ℂ ℂ ℂ) (n : ℕ) :
    (p - C • q).coeff n = p.coeff n - C * q.coeff n := by
  change (p n - (C • q) n) 1 = p n 1 - C * q.coeff n
  rw [FormalMultilinearSeries.smul_apply]
  rw [ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.smul_apply]
  change p.coeff n - C • q.coeff n = p.coeff n - C * q.coeff n
  simp [smul_eq_mul]

lemma coeff_schroederOneSubSeriesℂ_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    (PowerSeries.toFMLS schroederOneSubSeriesℂ).coeff n = 0 := by
  rw [PowerSeries.coeff_toFMLS]
  simp [schroederOneSubSeriesℂ, PowerSeries.coeff_X, PowerSeries.coeff_one,
    ne_of_gt (lt_of_lt_of_le (by norm_num : 0 < 2) hn),
    ne_of_gt (lt_of_lt_of_le (by norm_num : 1 < 2) hn)]

lemma coeff_schroederAdjustedRescaledFMLS_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    schroederAdjustedRescaledFMLS.coeff n =
      (PowerSeries.toFMLS schroederCenteredRescaledSeriesℂ).coeff n := by
  rw [schroederAdjustedRescaledFMLS, coeff_sub_const_smul,
    coeff_schroederOneSubSeriesℂ_of_two_le hn]
  ring

lemma hasFPowerSeriesAt_schroederOneSub_toFMLS :
    HasFPowerSeriesAt (fun z : ℂ => 1 - z)
      (PowerSeries.toFMLS schroederOneSubSeriesℂ) (0 : ℂ) := by
  have hconst := hasFPowerSeriesAt_const_toFMLS_C (1 : ℂ)
  have hid := hasFPowerSeriesAt_id_toFMLS_X
  have hsub := hconst.sub hid
  simpa [schroederOneSubSeriesℂ, toFMLS_sub] using hsub

theorem schroederAdjustedRescaledFun_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt schroederAdjustedRescaledFun
      schroederAdjustedRescaledFMLS (0 : ℂ) := by
  have hlin := hasFPowerSeriesAt_schroederOneSub_toFMLS.const_smul
    (c := schroederAnalyticLinearCoeff)
  have hsub := schroederCenteredRescaledFun_hasFPowerSeriesAt_zero.sub hlin
  simpa [schroederAdjustedRescaledFun, schroederAdjustedRescaledFMLS, smul_eq_mul] using hsub

lemma analyticOnNhd_schroederAdjustedRescaledFun :
    AnalyticOnNhd ℂ schroederAdjustedRescaledFun
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
  have hlinear : AnalyticOnNhd ℂ
      (fun z : ℂ => schroederAnalyticLinearCoeff * (1 - z))
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
    simpa [smul_eq_mul] using
      (analyticOnNhd_const.mul (analyticOnNhd_const.sub analyticOnNhd_id))
  simpa [schroederAdjustedRescaledFun] using
    analyticOnNhd_schroederCenteredRescaledFun.sub hlinear

lemma schroederSqrtRegular_one :
    schroederSqrtRegular (1 : ℂ) = schroederSqrtRegularAtOneℂ := by
  unfold schroederSqrtRegular schroederRhoℂ
  simpa [Complex.ofReal_sub, Complex.ofReal_pow] using
    Complex_cpow_one_sub_schroederRho_sq_half

lemma schroederSqrtRegularAtOne_sq :
    schroederSqrtRegularAtOneℂ ^ 2 = 1 - schroederRhoℂ ^ 2 := by
  have h := schroederSqrtRegular_sq (1 : ℂ)
  rwa [schroederSqrtRegular_one, mul_one] at h

lemma schroederSqrtRegularAtOne_ne_zero :
    schroederSqrtRegularAtOneℂ ≠ 0 := by
  unfold schroederSqrtRegularAtOneℂ
  exact_mod_cast (Real.sqrt_ne_zero'.mpr one_sub_schroederRho_sq_pos)

lemma schroederSecondK_mul_sqrt :
    schroederSecondKℂ * schroederSqrtRegularAtOneℂ =
      2 - schroederRhoℂ ^ 2 := by
  unfold schroederSecondKℂ
  field_simp [schroederSqrtRegularAtOne_ne_zero]

private lemma hasDerivAt_one_sub :
    HasDerivAt (fun z : ℂ => 1 - z) (-1 : ℂ) (1 : ℂ) := by
  have hid : HasDerivAt (fun z : ℂ => z) 1 (1 : ℂ) := by
    simpa using hasDerivAt_id (1 : ℂ)
  have h := (hasDerivAt_const (1 : ℂ) (1 : ℂ)).sub hid
  simpa only [Pi.sub_apply, zero_sub] using h

private lemma hasDerivAt_one_sub_rho_mul :
    HasDerivAt (fun z : ℂ => 1 - schroederRhoℂ * z)
      (-schroederRhoℂ) (1 : ℂ) := by
  have hid : HasDerivAt (fun z : ℂ => z) 1 (1 : ℂ) := by
    simpa using hasDerivAt_id (1 : ℂ)
  have h := (hasDerivAt_const (1 : ℂ) (1 : ℂ)).sub
    (HasDerivAt.const_mul schroederRhoℂ hid)
  simpa only [Pi.sub_apply, zero_sub, mul_one] using h

lemma hasDerivAt_schroederSqrtRegular_one :
    HasDerivAt schroederSqrtRegular
      (-(schroederRhoℂ ^ 2) / (2 * schroederSqrtRegularAtOneℂ)) (1 : ℂ) := by
  have hid : HasDerivAt (fun z : ℂ => z) 1 (1 : ℂ) := by
    simpa using hasDerivAt_id (1 : ℂ)
  have hbase : HasDerivAt (fun z : ℂ => 1 - schroederRhoℂ ^ 2 * z)
      (-(schroederRhoℂ ^ 2)) (1 : ℂ) := by
    have h := (hasDerivAt_const (1 : ℂ) (1 : ℂ)).sub
      (HasDerivAt.const_mul (schroederRhoℂ ^ 2) hid)
    simpa only [Pi.sub_apply, zero_sub, mul_one] using h
  have hslit : (1 : ℂ) - schroederRhoℂ ^ 2 * (1 : ℂ) ∈ Complex.slitPlane := by
    convert Complex.ofReal_mem_slitPlane.2 one_sub_schroederRho_sq_pos using 1
    simp [schroederRhoℂ, Complex.ofReal_sub, Complex.ofReal_pow]
  have hpow := hbase.cpow_const (c := (1 / 2 : ℂ)) hslit
  convert hpow using 1
  · rw [show (1 / 2 : ℂ) - 1 = -(1 / 2 : ℂ) by norm_num]
    rw [Complex.cpow_neg]
    rw [show ((1 : ℂ) - schroederRhoℂ ^ 2 * (1 : ℂ)) ^ (1 / 2 : ℂ) =
        schroederSqrtRegularAtOneℂ by
        simpa [schroederSqrtRegular] using schroederSqrtRegular_one]
    field_simp [schroederSqrtRegularAtOne_ne_zero]

def schroederSecondNoS (z : ℂ) : ℂ :=
  -2 * schroederOneSubRhoℂ * schroederSqrtRegular z +
    2 * schroederSqrtRegularAtOneℂ * (1 - schroederRhoℂ * z) -
    2 * schroederSqrtRegular z * (1 - z) +
    schroederSecondKℂ * (1 - z) * (1 - schroederRhoℂ * z)

def schroederSecondSqrtCoeff (z : ℂ) : ℂ :=
  -2 * schroederOneSubRhoℂ * schroederRhoℂ +
    2 * schroederSqrtRegularAtOneℂ * schroederSqrtRegular z -
    2 * (1 - schroederRhoℂ * z) +
    schroederSecondKℂ * (1 - z) * schroederSqrtRegular z

lemma schroederOneSubRhoℂ_eq :
    schroederOneSubRhoℂ = 1 - schroederRhoℂ := by
  simp [schroederOneSubRhoℂ, schroederRhoℂ, Complex.ofReal_sub]

lemma schroederSecondNoS_one :
    schroederSecondNoS (1 : ℂ) = 0 := by
  unfold schroederSecondNoS
  rw [schroederSqrtRegular_one]
  rw [schroederOneSubRhoℂ_eq]
  ring

lemma schroederSecondSqrtCoeff_one :
    schroederSecondSqrtCoeff (1 : ℂ) = 0 := by
  unfold schroederSecondSqrtCoeff
  rw [schroederSqrtRegular_one]
  rw [schroederOneSubRhoℂ_eq]
  ring_nf
  rw [schroederSqrtRegularAtOne_sq]
  ring

lemma schroederSecondNoS_deriv_expr :
    -2 * schroederOneSubRhoℂ *
        (-(schroederRhoℂ ^ 2) / (2 * schroederSqrtRegularAtOneℂ)) +
      2 * schroederSqrtRegularAtOneℂ * (-schroederRhoℂ) +
      (-2) *
        ((-(schroederRhoℂ ^ 2) / (2 * schroederSqrtRegularAtOneℂ)) *
            ((1 : ℂ) - 1) +
          schroederSqrtRegularAtOneℂ * (-1)) +
      schroederSecondKℂ *
        ((-1) * ((1 : ℂ) - schroederRhoℂ * 1) +
          ((1 : ℂ) - 1) * (-schroederRhoℂ)) = 0 := by
  unfold schroederSecondKℂ
  rw [schroederOneSubRhoℂ_eq]
  field_simp [schroederSqrtRegularAtOne_ne_zero]
  rw [schroederSqrtRegularAtOne_sq]
  ring

lemma hasDerivAt_schroederSecondNoS_one :
    HasDerivAt schroederSecondNoS 0 (1 : ℂ) := by
  have ht := hasDerivAt_schroederSqrtRegular_one
  have h1 := HasDerivAt.const_mul (-2 * schroederOneSubRhoℂ) ht
  have h2 := HasDerivAt.const_mul (2 * schroederSqrtRegularAtOneℂ)
    hasDerivAt_one_sub_rho_mul
  have h3 := HasDerivAt.const_mul (-2 : ℂ) (ht.mul hasDerivAt_one_sub)
  have h4 := HasDerivAt.const_mul schroederSecondKℂ
    (hasDerivAt_one_sub.mul hasDerivAt_one_sub_rho_mul)
  have hcalc := ((h1.add h2).add h3).add h4
  convert hcalc using 1
  · ext z
    simp [schroederSecondNoS]
    ring
  · rw [schroederSqrtRegular_one]
    exact schroederSecondNoS_deriv_expr.symm

lemma hasDerivAt_schroederSecondSqrtCoeff_one :
    HasDerivAt schroederSecondSqrtCoeff
      (2 * schroederSqrtRegularAtOneℂ *
          (-(schroederRhoℂ ^ 2) / (2 * schroederSqrtRegularAtOneℂ)) -
        2 * (-schroederRhoℂ) +
        schroederSecondKℂ *
          ((-1) * schroederSqrtRegularAtOneℂ +
            ((1 : ℂ) - 1) *
              (-(schroederRhoℂ ^ 2) / (2 * schroederSqrtRegularAtOneℂ))))
      (1 : ℂ) := by
  have ht := hasDerivAt_schroederSqrtRegular_one
  have hconst : HasDerivAt
      (fun _ : ℂ => -2 * schroederOneSubRhoℂ * schroederRhoℂ) 0 (1 : ℂ) :=
    hasDerivAt_const (1 : ℂ) _
  have h2 := HasDerivAt.const_mul (2 * schroederSqrtRegularAtOneℂ) ht
  have h3 := HasDerivAt.const_mul (-2 : ℂ) hasDerivAt_one_sub_rho_mul
  have h4 := HasDerivAt.const_mul schroederSecondKℂ
    (hasDerivAt_one_sub.mul ht)
  have hcalc := ((hconst.add h2).add h3).add h4
  convert hcalc using 1
  · ext z
    simp [schroederSecondSqrtCoeff]
    ring
  · rw [schroederSqrtRegular_one]
    ring

private lemma nhdsWithin_schroeder_delta_le_punctured :
    𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ) ≤
      𝓝[({1}ᶜ : Set ℂ)] (1 : ℂ) := by
  exact nhdsWithin_mono _ (by intro z hz; exact hz.2.1)

lemma tendsto_schroederSecondNoS_div :
    Tendsto (fun z : ℂ => schroederSecondNoS z / (1 - z))
      (𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)) (𝓝 0) := by
  let l := 𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)
  have hslope : Tendsto (slope schroederSecondNoS (1 : ℂ)) l (𝓝 (0 : ℂ)) :=
    hasDerivAt_schroederSecondNoS_one.tendsto_slope.mono_left
      nhdsWithin_schroeder_delta_le_punctured
  have hneg : Tendsto (fun z : ℂ => -slope schroederSecondNoS (1 : ℂ) z) l
      (𝓝 (0 : ℂ)) := by
    simpa using hslope.neg
  refine hneg.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz_ne : z ≠ 1 := hz.2.1
  have h1z : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz_ne)
  have hz1 : z - (1 : ℂ) ≠ 0 := sub_ne_zero.mpr hz_ne
  simp [slope, schroederSecondNoS_one, div_eq_mul_inv]
  field_simp [h1z, hz1]
  ring

lemma tendsto_schroederSecondSqrtCoeff_div :
    Tendsto (fun z : ℂ => schroederSecondSqrtCoeff z / (1 - z))
      (𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ))
      (𝓝 (-(2 * schroederSqrtRegularAtOneℂ *
          (-(schroederRhoℂ ^ 2) / (2 * schroederSqrtRegularAtOneℂ)) -
        2 * (-schroederRhoℂ) +
        schroederSecondKℂ *
          ((-1) * schroederSqrtRegularAtOneℂ +
            ((1 : ℂ) - 1) *
              (-(schroederRhoℂ ^ 2) / (2 * schroederSqrtRegularAtOneℂ)))))) := by
  let l := 𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)
  have hslope := hasDerivAt_schroederSecondSqrtCoeff_one.tendsto_slope.mono_left
    nhdsWithin_schroeder_delta_le_punctured
  have hneg := hslope.neg
  refine hneg.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz_ne : z ≠ 1 := hz.2.1
  have h1z : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz_ne)
  have hz1 : z - (1 : ℂ) ≠ 0 := sub_ne_zero.mpr hz_ne
  simp [slope, schroederSecondSqrtCoeff_one, div_eq_mul_inv]
  field_simp [h1z, hz1]
  ring

lemma schroederSecondQuotient_decomp (z : ℂ) :
    schroederSingularityQuotientModel z -
        schroederAnalyticLinearCoeff * schroederSqrtOneSub z -
        schroederSecondSingularCoeff * (1 - z) =
      (schroederSecondNoS z +
          schroederSqrtOneSub z * schroederSecondSqrtCoeff z) /
        (schroederOneSubRhoℂ ^ 2 * schroederRescaledDenominator z) := by
  set s := schroederSqrtOneSub z with hs_def
  set t := schroederSqrtRegular z with ht_def
  have hs_sq : s ^ 2 = 1 - z := by
    rw [hs_def]
    exact schroederSqrtOneSub_sq z
  have hd := schroederRescaledDenominator_ne_zero z
  have hd' : 1 - schroederRhoℂ * z + s * t ≠ 0 := by
    rw [mul_comm s t]
    simpa [schroederRescaledDenominator, hs_def, ht_def] using hd
  have ha := one_sub_schroederRho_ne_zeroℂ
  unfold schroederSingularityQuotientModel schroederSecondNoS
    schroederSecondSqrtCoeff schroederAnalyticLinearCoeff
    schroederSecondSingularCoeff schroederSecondKℂ schroederSingularCoeff
    schroederRescaledDenominator
  rw [← hs_def, ← ht_def]
  field_simp [hd, hd', ha, schroederSqrtRegularAtOne_ne_zero]
  rw [← hs_sq]
  ring

lemma schroederSecondQuotient_div_eq {z : ℂ} (hz : z ≠ 1) :
    (schroederSingularityQuotientModel z -
        schroederAnalyticLinearCoeff * schroederSqrtOneSub z -
        schroederSecondSingularCoeff * (1 - z)) / (1 - z) =
      (schroederSecondNoS z / (1 - z) +
          schroederSqrtOneSub z * (schroederSecondSqrtCoeff z / (1 - z))) /
        (schroederOneSubRhoℂ ^ 2 * schroederRescaledDenominator z) := by
  rw [schroederSecondQuotient_decomp z]
  have h1z : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  have hd := schroederRescaledDenominator_ne_zero z
  have ha := one_sub_schroederRho_ne_zeroℂ
  field_simp [h1z, hd, ha]

lemma tendsto_schroederSecondQuotient_div :
    Tendsto
      (fun z : ℂ =>
        (schroederSingularityQuotientModel z -
          schroederAnalyticLinearCoeff * schroederSqrtOneSub z -
          schroederSecondSingularCoeff * (1 - z)) / (1 - z))
      (𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)) (𝓝 0) := by
  let l := 𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)
  have hnum : Tendsto
      (fun z : ℂ =>
        schroederSecondNoS z / (1 - z) +
          schroederSqrtOneSub z * (schroederSecondSqrtCoeff z / (1 - z))) l
      (𝓝 (0 + 0 * (-(2 * schroederSqrtRegularAtOneℂ *
          (-(schroederRhoℂ ^ 2) / (2 * schroederSqrtRegularAtOneℂ)) -
        2 * (-schroederRhoℂ) +
        schroederSecondKℂ *
          ((-1) * schroederSqrtRegularAtOneℂ +
            ((1 : ℂ) - 1) *
              (-(schroederRhoℂ ^ 2) / (2 * schroederSqrtRegularAtOneℂ))))))) := by
    exact tendsto_schroederSecondNoS_div.add
      (tendsto_schroederSqrtOneSub.mul tendsto_schroederSecondSqrtCoeff_div)
  have hden : Tendsto
      (fun z : ℂ => schroederOneSubRhoℂ ^ 2 * schroederRescaledDenominator z) l
      (𝓝 (schroederOneSubRhoℂ ^ 2 * schroederOneSubRhoℂ)) := by
    exact tendsto_const_nhds.mul tendsto_schroederRescaledDenominator
  have hden_ne :
      schroederOneSubRhoℂ ^ 2 * schroederOneSubRhoℂ ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 one_sub_schroederRho_ne_zeroℂ)
      one_sub_schroederRho_ne_zeroℂ
  have hquot := hnum.div hden hden_ne
  have hquot0 : Tendsto
      (fun z : ℂ =>
        (schroederSecondNoS z / (1 - z) +
            schroederSqrtOneSub z * (schroederSecondSqrtCoeff z / (1 - z))) /
          (schroederOneSubRhoℂ ^ 2 * schroederRescaledDenominator z)) l (𝓝 0) := by
    convert hquot using 1
    norm_num
  refine hquot0.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (schroederSecondQuotient_div_eq hz.2.1).symm

lemma tendsto_schroederSecondQuotient_twoTerm :
    Tendsto
      (fun z : ℂ =>
        ‖schroederSingularityQuotientModel z -
            schroederAnalyticLinearCoeff * schroederSqrtOneSub z -
            schroederSecondSingularCoeff * (1 - z)‖ *
          ‖(1 : ℂ) - z‖ ^ (-(1 : ℝ)))
      (𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)) (𝓝 0) := by
  let l := 𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)
  have hnorm : Tendsto
      (fun z : ℂ =>
        ‖(schroederSingularityQuotientModel z -
          schroederAnalyticLinearCoeff * schroederSqrtOneSub z -
          schroederSecondSingularCoeff * (1 - z)) / (1 - z)‖) l (𝓝 0) := by
    simpa using tendsto_schroederSecondQuotient_div.norm
  refine hnorm.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz_ne : z ≠ 1 := hz.2.1
  have h1z : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz_ne)
  rw [Real.rpow_neg (norm_nonneg ((1 : ℂ) - z)), Real.rpow_one]
  rw [show
      ‖schroederSingularityQuotientModel z -
          schroederAnalyticLinearCoeff * schroederSqrtOneSub z -
          schroederSecondSingularCoeff * (1 - z)‖ * ‖(1 : ℂ) - z‖⁻¹ =
        ‖schroederSingularityQuotientModel z -
          schroederAnalyticLinearCoeff * schroederSqrtOneSub z -
          schroederSecondSingularCoeff * (1 - z)‖ / ‖(1 : ℂ) - z‖ by
        rw [div_eq_mul_inv]]
  rw [← norm_div]

lemma schroeder_adjusted_residual_eq {z : ℂ} (hz : z ≠ 1) :
    schroederAdjustedRescaledFun z -
        schroederSingularCoeff * (1 - z) ^ (1 / 2 : ℂ) -
        schroederSecondSingularCoeff * (1 - z) ^ (3 / 2 : ℂ) =
      schroederSqrtOneSub z *
        (schroederSingularityQuotientModel z -
          schroederAnalyticLinearCoeff * schroederSqrtOneSub z -
          schroederSecondSingularCoeff * (1 - z)) := by
  let s := schroederSqrtOneSub z
  have hs_ne : s ≠ 0 := by
    dsimp [s]
    exact schroederSqrtOneSub_ne_zero_of_ne_one hz
  have hQ := schroeder_singularity_quotient_eq hz
  have hcenter : schroederCenteredRescaledFun z - schroederSingularCoeff * s =
      schroederSingularityQuotientModel z * s := by
    have hmul := congrArg (fun w : ℂ => w * s) hQ
    dsimp [s] at hmul ⊢
    rw [div_mul_cancel₀ _ hs_ne] at hmul
    exact hmul
  have hs_sq : s ^ 2 = 1 - z := by
    dsimp [s]
    exact schroederSqrtOneSub_sq z
  have hu_ne : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  have hpow_three_halves : (1 - z) ^ (3 / 2 : ℂ) = (1 - z) * s := by
    dsimp [s]
    rw [show (3 / 2 : ℂ) = 1 + (1 / 2 : ℂ) by norm_num]
    rw [Complex.cpow_add _ _ hu_ne, Complex.cpow_one]
    rfl
  unfold schroederAdjustedRescaledFun
  change schroederCenteredRescaledFun z - schroederAnalyticLinearCoeff * (1 - z) -
      schroederSingularCoeff * schroederSqrtOneSub z -
      schroederSecondSingularCoeff * (1 - z) ^ (3 / 2 : ℂ) =
    schroederSqrtOneSub z *
      (schroederSingularityQuotientModel z -
        schroederAnalyticLinearCoeff * schroederSqrtOneSub z -
        schroederSecondSingularCoeff * (1 - z))
  rw [hpow_three_halves]
  rw [show schroederCenteredRescaledFun z - schroederAnalyticLinearCoeff * (1 - z) -
      schroederSingularCoeff * schroederSqrtOneSub z -
      schroederSecondSingularCoeff * ((1 - z) * schroederSqrtOneSub z) =
      (schroederCenteredRescaledFun z - schroederSingularCoeff * schroederSqrtOneSub z) -
        schroederAnalyticLinearCoeff * (1 - z) -
        schroederSecondSingularCoeff * ((1 - z) * schroederSqrtOneSub z) by ring]
  dsimp [s] at hcenter hs_sq
  rw [hcenter]
  rw [← hs_sq]
  ring

lemma schroeder_adjusted_singularity_twoTerm_norm_eq {z : ℂ} (hz : z ≠ 1) :
    ‖schroederAdjustedRescaledFun z -
        schroederSingularCoeff * (1 - z) ^ (1 / 2 : ℂ) -
        schroederSecondSingularCoeff * (1 - z) ^ (3 / 2 : ℂ)‖ *
      ‖(1 : ℂ) - z‖ ^ (-(3 / 2 : ℝ)) =
    ‖schroederSingularityQuotientModel z -
        schroederAnalyticLinearCoeff * schroederSqrtOneSub z -
        schroederSecondSingularCoeff * (1 - z)‖ *
      ‖(1 : ℂ) - z‖ ^ (-(1 : ℝ)) := by
  let u : ℂ := 1 - z
  have hu_ne : u ≠ 0 := by
    dsimp [u]
    exact sub_ne_zero.mpr (Ne.symm hz)
  have hu_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu_ne
  have hs_norm : ‖schroederSqrtOneSub z‖ = ‖u‖ ^ (1 / 2 : ℝ) := by
    dsimp [u]
    unfold schroederSqrtOneSub
    convert Complex.norm_cpow_real ((1 : ℂ) - z) (1 / 2 : ℝ) using 1
    norm_num
  rw [schroeder_adjusted_residual_eq hz]
  rw [norm_mul, hs_norm]
  change (‖u‖ ^ (1 / 2 : ℝ) *
        ‖schroederSingularityQuotientModel z -
          schroederAnalyticLinearCoeff * schroederSqrtOneSub z -
          schroederSecondSingularCoeff * (1 - z)‖) *
      ‖u‖ ^ (-(3 / 2 : ℝ)) =
    ‖schroederSingularityQuotientModel z -
        schroederAnalyticLinearCoeff * schroederSqrtOneSub z -
        schroederSecondSingularCoeff * (1 - z)‖ *
      ‖u‖ ^ (-(1 : ℝ))
  have hpow : ‖u‖ ^ (1 / 2 : ℝ) * ‖u‖ ^ (-(3 / 2 : ℝ)) =
      ‖u‖ ^ (-(1 : ℝ)) := by
    rw [← Real.rpow_add hu_pos]
    norm_num
  rw [show ‖u‖ ^ (1 / 2 : ℝ) *
        ‖schroederSingularityQuotientModel z -
          schroederAnalyticLinearCoeff * schroederSqrtOneSub z -
          schroederSecondSingularCoeff * (1 - z)‖ * ‖u‖ ^ (-(3 / 2 : ℝ)) =
      ‖schroederSingularityQuotientModel z -
          schroederAnalyticLinearCoeff * schroederSqrtOneSub z -
          schroederSecondSingularCoeff * (1 - z)‖ *
        (‖u‖ ^ (1 / 2 : ℝ) * ‖u‖ ^ (-(3 / 2 : ℝ))) by ring, hpow]

lemma schroederAdjustedRescaledFun_singularity_twoTerm :
    Tendsto
      (fun z : ℂ =>
        ‖schroederAdjustedRescaledFun z -
            schroederSingularCoeff * (1 - z) ^ (1 / 2 : ℂ) -
            schroederSecondSingularCoeff * (1 - z) ^ (3 / 2 : ℂ)‖ *
          ‖(1 : ℂ) - z‖ ^ (-(3 / 2 : ℝ)))
      (𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)) (𝓝 0) := by
  refine tendsto_schroederSecondQuotient_twoTerm.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (schroeder_adjusted_singularity_twoTerm_norm_eq hz.2.1).symm

lemma schroeder_neg_half_pole :
    ∀ m : ℕ, (-(1 / 2 : ℝ)) ≠ 1 - (m : ℝ) := by
  intro m h
  have hm2R : (2 * m : ℝ) = 3 := by nlinarith
  have hm2N : 2 * m = 3 := by exact_mod_cast hm2R
  omega

lemma schroeder_Real_Gamma_neg_half :
    Real.Gamma (-(1 / 2 : ℝ)) = -2 * Real.sqrt Real.pi := by
  have h := Real.Gamma_add_one (s := (-(1 / 2 : ℝ)))
    (by norm_num : (-(1 / 2 : ℝ)) ≠ 0)
  norm_num at h
  rw [Real.Gamma_one_half_eq] at h
  linarith

lemma schroeder_Real_Gamma_neg_three_halves :
    Real.Gamma (-(3 / 2 : ℝ)) = 4 * Real.sqrt Real.pi / 3 := by
  have h := Real.Gamma_add_one (s := (-(3 / 2 : ℝ)))
    (by norm_num : (-(3 / 2 : ℝ)) ≠ 0)
  norm_num at h
  rw [schroeder_Real_Gamma_neg_half] at h
  nlinarith

lemma schroederSecondSingularCoeff_eq_ratio :
    schroederSecondSingularCoeff =
      schroederSingularCoeff * ((schroederSecondSingularRatio : ℝ) : ℂ) := by
  unfold schroederSecondSingularCoeff schroederSecondKℂ schroederSingularCoeff
  field_simp [schroederSqrtRegularAtOne_ne_zero,
    pow_ne_zero 2 one_sub_schroederRho_ne_zeroℂ]
  rw [schroederSqrtRegularAtOne_sq]
  unfold schroederSecondSingularRatio schroederRhoℂ schroederRho
  norm_num [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul,
    Complex.ofReal_div, Complex.ofReal_pow]
  ring_nf
  have hsqrt2_sq_complex : (((Real.sqrt 2 : ℝ) : ℂ) ^ 2) = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hsqrt2_cu_complex :
      (((Real.sqrt 2 : ℝ) : ℂ) ^ 3) = 2 * ((Real.sqrt 2 : ℝ) : ℂ) := by
    rw [show (((Real.sqrt 2 : ℝ) : ℂ) ^ 3) =
        ((Real.sqrt 2 : ℝ) : ℂ) * (((Real.sqrt 2 : ℝ) : ℂ) ^ 2) by ring,
      hsqrt2_sq_complex]
    ring
  rw [hsqrt2_cu_complex, hsqrt2_sq_complex]
  ring

lemma schroederRelativeSecondConstant_eq_transfer :
    schroederRelativeSecondConstant =
      3 / 8 - (3 / 2) * schroederSecondSingularRatio := by
  unfold schroederRelativeSecondConstant schroederSecondSingularRatio
  ring

lemma schroeder_transfer_constant_realGamma_complex :
    schroederSingularCoeff *
        (((1 / Real.Gamma (-(1 / 2 : ℝ)) : ℝ) : ℂ)) =
      ((schroederAsymptoticConstant : ℝ) : ℂ) := by
  rw [schroeder_Real_Gamma_neg_half, schroederAsymptoticConstant_complex,
    schroederSingularCoeff]
  have hsqrtπ_ne : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr Real.pi_pos)
  have hone_ne : schroederOneSubRhoℂ ^ 2 ≠ 0 := by
    exact pow_ne_zero 2 one_sub_schroederRho_ne_zeroℂ
  norm_num [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_mul]
  field_simp [hsqrtπ_ne, hone_ne]

lemma schroeder_second_model_constant_complex :
    schroederSingularCoeff *
        (((((-(1 / 2 : ℝ)) * ((-(1 / 2 : ℝ)) - 1) / 2 /
              Real.Gamma (-(1 / 2 : ℝ))) : ℝ) : ℂ)) +
      schroederSecondSingularCoeff *
        (((1 / Real.Gamma ((-(1 / 2 : ℝ)) - 1) : ℝ) : ℂ)) =
      ((schroederSecondAsymptoticConstant : ℝ) : ℂ) := by
  rw [show (-(1 / 2 : ℝ)) - 1 = -(3 / 2 : ℝ) by norm_num]
  rw [schroeder_Real_Gamma_neg_half, schroeder_Real_Gamma_neg_three_halves]
  rw [schroederSecondSingularCoeff_eq_ratio]
  rw [schroederSecondAsymptoticConstant, Complex.ofReal_mul,
    ← schroeder_transfer_constant_realGamma_complex]
  rw [schroeder_Real_Gamma_neg_half]
  rw [schroederRelativeSecondConstant_eq_transfer]
  unfold schroederSecondSingularRatio
  have hsqrtπ_ne : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr Real.pi_pos)
  norm_num [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul,
    Complex.ofReal_div]
  field_simp [hsqrtπ_ne]
  ring

lemma schroeder_secondOrder_model_complex_eq (n : ℕ) :
    (schroederSingularCoeff *
        ((((n : ℝ) ^ ((-(1 / 2 : ℝ)) - 1) /
              Real.Gamma (-(1 / 2 : ℝ)) : ℝ) : ℂ) +
          ((((-(1 / 2 : ℝ)) * ((-(1 / 2 : ℝ)) - 1) / 2 /
                Real.Gamma (-(1 / 2 : ℝ))) *
              (n : ℝ) ^ ((-(1 / 2 : ℝ)) - 2) : ℝ) : ℂ)) +
      schroederSecondSingularCoeff *
        (((n : ℝ) ^ ((-(1 / 2 : ℝ)) - 2) /
          Real.Gamma ((-(1 / 2 : ℝ)) - 1) : ℝ) : ℂ)) =
      (((schroederAsymptoticConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
          schroederSecondAsymptoticConstant * (n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ)) := by
  have hpow1 : (n : ℝ) ^ ((-(1 / 2 : ℝ)) - 1) =
      (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
    congr 1
    norm_num
  have hpow2 : (n : ℝ) ^ ((-(1 / 2 : ℝ)) - 2) =
      (n : ℝ) ^ (-(5 / 2 : ℝ)) := by
    congr 1
    norm_num
  rw [hpow1, hpow2]
  rw [show (-(1 / 2 : ℝ)) - 1 = -(3 / 2 : ℝ) by norm_num]
  have hfirst := schroeder_transfer_constant_realGamma_complex
  have hsecond := schroeder_second_model_constant_complex
  norm_num [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_div] at hfirst hsecond ⊢
  rw [← hfirst, ← hsecond]
  ring

theorem schroederAdjustedRescaledCoeff_secondOrder :
    (fun n : ℕ =>
      schroederAdjustedRescaledFMLS.coeff n -
        (((schroederAsymptoticConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
            schroederSecondAsymptoticConstant * (n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ)))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(5 / 2 : ℝ))) := by
  have htransfer := transfer_twoTerm_secondOrder_general
    (α := (-(1 / 2 : ℝ))) (C0 := schroederSingularCoeff)
    (C1 := schroederSecondSingularCoeff)
    (R := (3 / 2 : ℝ)) (φ := Real.pi / 4)
    (f := schroederAdjustedRescaledFun) (p := schroederAdjustedRescaledFMLS)
    schroeder_neg_half_pole (by norm_num) (by positivity) ?_
    schroederAdjustedRescaledFun_hasFPowerSeriesAt_zero
    analyticOnNhd_schroederAdjustedRescaledFun ?_
  · have hcomplex :
        (fun n : ℕ =>
          schroederAdjustedRescaledFMLS.coeff n -
            (((schroederAsymptoticConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
                schroederSecondAsymptoticConstant * (n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ)))
          =o[atTop] (fun n : ℕ => (n : ℝ) ^ ((-(1 / 2 : ℝ)) - 2)) := by
      refine htransfer.congr_left ?_
      intro n
      rw [schroeder_secondOrder_model_complex_eq n]
    convert hcomplex using 1
    ext n
    congr 1
    norm_num
  · nlinarith [Real.pi_pos]
  · convert schroederAdjustedRescaledFun_singularity_twoTerm using 1
    ext z
    norm_num

theorem schroederCenteredRescaledCoeff_secondOrder :
    (fun n : ℕ =>
      (PowerSeries.toFMLS schroederCenteredRescaledSeriesℂ).coeff n -
        (((schroederAsymptoticConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
            schroederSecondAsymptoticConstant * (n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ)))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(5 / 2 : ℝ))) := by
  have h := schroederAdjustedRescaledCoeff_secondOrder
  refine h.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_ge_atTop 2] with n hn
  rw [coeff_schroederAdjustedRescaledFMLS_of_two_le hn]

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

theorem schroederRescaled_complex_secondOrder :
    (fun n : ℕ =>
      (schroeder n : ℂ) * schroederRhoℂ ^ n -
        (((schroederAsymptoticConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
            schroederSecondAsymptoticConstant * (n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ)))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(5 / 2 : ℝ))) := by
  have hcenter := schroederCenteredRescaledCoeff_secondOrder
  refine hcenter.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_ne_atTop 0] with n hn
  rw [PowerSeries.coeff_toFMLS, coeff_schroederCenteredRescaledSeriesℂ_of_ne_zero hn,
    coeff_schroederRescaledSeriesℂ]
  rw [show schroederRhoℂ ^ n = (((schroederRho ^ n : ℝ) : ℂ)) by
    unfold schroederRhoℂ
    rw [Complex.ofReal_pow]]
  rw [Complex.ofReal_pow]

theorem schroederRescaled_secondOrder :
    (fun n : ℕ =>
      (schroeder n : ℝ) * schroederRho ^ n -
        (schroederAsymptoticConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
          schroederSecondAsymptoticConstant * (n : ℝ) ^ (-(5 / 2 : ℝ))))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(5 / 2 : ℝ))) := by
  have hcomplex :
      (fun n : ℕ =>
        (((schroeder n : ℝ) * schroederRho ^ n : ℝ) : ℂ) -
          (((schroederAsymptoticConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
              schroederSecondAsymptoticConstant * (n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ)))
        =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(5 / 2 : ℝ))) := by
    refine schroederRescaled_complex_secondOrder.congr_left ?_
    intro n
    have hpow : schroederRhoℂ ^ n = (((schroederRho ^ n : ℝ) : ℂ)) := by
      unfold schroederRhoℂ
      rw [Complex.ofReal_pow]
    have hcoeff :
        (schroeder n : ℂ) * schroederRhoℂ ^ n =
          (((schroeder n : ℝ) * schroederRho ^ n : ℝ) : ℂ) := by
      rw [hpow]
      norm_num [Complex.ofReal_mul]
    rw [hcoeff]
  have hreal := complex_re_isLittleO_ofReal hcomplex
  refine hreal.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards with n
  rw [Complex.ofReal_re]

theorem schroeder_secondOrder_additive :
    (fun n : ℕ =>
      (schroeder n : ℝ) -
        schroederRho⁻¹ ^ n *
          (schroederAsymptoticConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
            schroederSecondAsymptoticConstant * (n : ℝ) ^ (-(5 / 2 : ℝ))))
      =o[atTop]
        (fun n : ℕ => schroederRho⁻¹ ^ n * (n : ℝ) ^ (-(5 / 2 : ℝ))) := by
  have hmul := schroederRescaled_secondOrder.mul_isBigO
    (isBigO_refl (fun n : ℕ => schroederRho⁻¹ ^ n) atTop)
  refine hmul.congr' ?_ ?_
  · filter_upwards with n
    calc
      ((schroeder n : ℝ) * schroederRho ^ n -
          (schroederAsymptoticConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
            schroederSecondAsymptoticConstant * (n : ℝ) ^ (-(5 / 2 : ℝ)))) *
          schroederRho⁻¹ ^ n
          = (schroeder n : ℝ) * (schroederRho ^ n * schroederRho⁻¹ ^ n) -
              schroederRho⁻¹ ^ n *
                (schroederAsymptoticConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
                  schroederSecondAsymptoticConstant * (n : ℝ) ^ (-(5 / 2 : ℝ))) := by
            ring
      _ = (schroeder n : ℝ) -
              schroederRho⁻¹ ^ n *
                (schroederAsymptoticConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
                  schroederSecondAsymptoticConstant * (n : ℝ) ^ (-(5 / 2 : ℝ))) := by
            rw [← mul_pow, mul_inv_cancel₀ schroederRho_ne_zero, one_pow, mul_one]
  · filter_upwards with n
    ring

theorem schroederSecondAsymptoticConstant_eq_relative :
    schroederSecondAsymptoticConstant =
      schroederAsymptoticConstant * schroederRelativeSecondConstant := rfl

theorem schroeder_secondOrder :
    (fun n : ℕ =>
      (schroeder n : ℝ) -
        schroederRho⁻¹ ^ n * schroederAsymptoticConstant *
          (n : ℝ) ^ (-(3 / 2 : ℝ)) *
          (1 + schroederRelativeSecondConstant * (n : ℝ) ^ (-(1 : ℝ))))
      =o[atTop]
        (fun n : ℕ => schroederRho⁻¹ ^ n * (n : ℝ) ^ (-(5 / 2 : ℝ))) := by
  refine schroeder_secondOrder_additive.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ)) hn)
  have hpow : (n : ℝ) ^ (-(5 / 2 : ℝ)) =
      (n : ℝ) ^ (-(3 / 2 : ℝ)) * (n : ℝ) ^ (-(1 : ℝ)) := by
    rw [← Real.rpow_add hnpos]
    norm_num
  rw [schroederSecondAsymptoticConstant_eq_relative, hpow]
  ring
