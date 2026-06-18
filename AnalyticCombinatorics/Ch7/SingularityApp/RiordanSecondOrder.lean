import AnalyticCombinatorics.Ch4.Analytic.TransferSecondOrderGeneral
import AnalyticCombinatorics.Ch7.SingularityApp.Riordan

/-!
# Second-order Riordan asymptotics

The centered rescaled Riordan function has an analytic linear term between the
two half-integer singular terms.  We subtract that linear term before applying
the general second-order transfer theorem; its coefficients vanish for `n ≥ 2`.
-/

set_option maxHeartbeats 1200000

open Complex Filter Asymptotics Set
open scoped Topology BigOperators PowerSeries

noncomputable section

def riordanAnalyticLinearCoeff : ℂ := (3 / 2 : ℂ)

def riordanSecondSingularCoeff : ℂ :=
  riordanSingularCoeff * (9 / 8 : ℂ)

def riordanRelativeSecondConstant : ℝ := -(21 / 16 : ℝ)

def riordanSecondAsymptoticConstant : ℝ :=
  -(63 * Real.sqrt 3 / (128 * Real.sqrt Real.pi))

def riordanOneSubSeriesℂ : PowerSeries ℂ :=
  (1 : PowerSeries ℂ) - PowerSeries.X

def riordanAdjustedRescaledFMLS : FormalMultilinearSeries ℂ ℂ ℂ :=
  PowerSeries.toFMLS riordanCenteredRescaledSeriesℂ -
    riordanAnalyticLinearCoeff • PowerSeries.toFMLS riordanOneSubSeriesℂ

def riordanAdjustedRescaledFun (z : ℂ) : ℂ :=
  riordanCenteredRescaledFun z - riordanAnalyticLinearCoeff * (1 - z)

private lemma coeff_sub_const_smul (C : ℂ)
    (p q : FormalMultilinearSeries ℂ ℂ ℂ) (n : ℕ) :
    (p - C • q).coeff n = p.coeff n - C * q.coeff n := by
  change (p n - (C • q) n) 1 = p n 1 - C * q.coeff n
  rw [FormalMultilinearSeries.smul_apply]
  rw [ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.smul_apply]
  change p.coeff n - C • q.coeff n = p.coeff n - C * q.coeff n
  simp [smul_eq_mul]

lemma coeff_riordanOneSubSeriesℂ_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    (PowerSeries.toFMLS riordanOneSubSeriesℂ).coeff n = 0 := by
  rw [PowerSeries.coeff_toFMLS]
  simp [riordanOneSubSeriesℂ, PowerSeries.coeff_X, PowerSeries.coeff_one,
    ne_of_gt (lt_of_lt_of_le (by norm_num : 0 < 2) hn),
    ne_of_gt (lt_of_lt_of_le (by norm_num : 1 < 2) hn)]

lemma coeff_riordanAdjustedRescaledFMLS_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    riordanAdjustedRescaledFMLS.coeff n =
      (PowerSeries.toFMLS riordanCenteredRescaledSeriesℂ).coeff n := by
  rw [riordanAdjustedRescaledFMLS, coeff_sub_const_smul,
    coeff_riordanOneSubSeriesℂ_of_two_le hn]
  ring

lemma hasFPowerSeriesAt_riordanOneSub_toFMLS :
    HasFPowerSeriesAt (fun z : ℂ => 1 - z)
      (PowerSeries.toFMLS riordanOneSubSeriesℂ) (0 : ℂ) := by
  have hconst := hasFPowerSeriesAt_const_toFMLS_C (1 : ℂ)
  have hid := hasFPowerSeriesAt_id_toFMLS_X
  have hsub := hconst.sub hid
  simpa [riordanOneSubSeriesℂ, toFMLS_sub] using hsub

theorem riordanAdjustedRescaledFun_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt riordanAdjustedRescaledFun
      riordanAdjustedRescaledFMLS (0 : ℂ) := by
  have hlin := hasFPowerSeriesAt_riordanOneSub_toFMLS.const_smul
    (c := riordanAnalyticLinearCoeff)
  have hsub := riordanCenteredRescaledFun_hasFPowerSeriesAt_zero.sub hlin
  simpa [riordanAdjustedRescaledFun, riordanAdjustedRescaledFMLS, smul_eq_mul] using hsub

lemma analyticOnNhd_riordanAdjustedRescaledFun :
    AnalyticOnNhd ℂ riordanAdjustedRescaledFun
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
  have hlinear : AnalyticOnNhd ℂ
      (fun z : ℂ => riordanAnalyticLinearCoeff * (1 - z))
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
    simpa [smul_eq_mul] using
      (analyticOnNhd_const.mul
        ((analyticOnNhd_const.sub analyticOnNhd_id)))
  simpa [riordanAdjustedRescaledFun] using
    analyticOnNhd_riordanCenteredRescaledFun.sub hlinear

def riordanSecondNoS (z : ℂ) : ℂ :=
  -2 * riordanSqrtPlus z -
    riordanSingularCoeff * riordanAℂ * (1 + z / 3) -
    riordanAℂ * riordanSecondSingularCoeff * (1 - z) * (1 + z / 3) -
    riordanAℂ * riordanAnalyticLinearCoeff * riordanSqrtPlus z * (1 - z)

def riordanSecondSqrtCoeff (z : ℂ) : ℂ :=
  (2 / 3 : ℂ) -
    riordanSingularCoeff * riordanAℂ * riordanSqrtPlus z -
    riordanAℂ * riordanAnalyticLinearCoeff * (1 + z / 3) -
    riordanAℂ * riordanSecondSingularCoeff * (1 - z) * riordanSqrtPlus z

lemma riordanSqrtPlus_one :
    riordanSqrtPlus (1 : ℂ) = riordanSqrtPlusAtOneℂ := by
  unfold riordanSqrtPlus riordanSqrtPlusAtOneℂ motzkinSqrtPlus
  rw [show (1 : ℂ) + 1 / 3 = ((4 / 3 : ℝ) : ℂ) by norm_num]
  exact Complex_cpow_four_thirds_half

lemma hasDerivAt_riordanSqrtPlus_one :
    HasDerivAt riordanSqrtPlus (((Real.sqrt 3 / 12 : ℝ) : ℂ)) (1 : ℂ) := by
  have hid : HasDerivAt (fun z : ℂ => z) 1 (1 : ℂ) := by
    simpa using hasDerivAt_id (1 : ℂ)
  have hbase0 := (hasDerivAt_const (1 : ℂ) (1 : ℂ)).add (hid.div_const (3 : ℂ))
  have hbase : HasDerivAt (fun z : ℂ => 1 + z / 3) (1 / 3 : ℂ) (1 : ℂ) := by
    simpa only [Pi.add_apply, zero_add] using hbase0
  have hslit : (1 : ℂ) + 1 / 3 ∈ Complex.slitPlane := by
    convert Complex.ofReal_mem_slitPlane.2 (by norm_num : (0 : ℝ) < 4 / 3) using 1
    norm_num
  have hpow := hbase.cpow_const (c := (1 / 2 : ℂ)) hslit
  convert hpow using 1
  rw [show (1 : ℂ) + 1 / 3 = ((4 / 3 : ℝ) : ℂ) by norm_num]
  rw [show (1 / 2 : ℂ) - 1 = -(1 / 2 : ℂ) by norm_num]
  rw [Complex.cpow_neg, Complex_cpow_four_thirds_half]
  have hs3 : ((Real.sqrt 3 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 3))
  norm_num [Complex.ofReal_div, Complex.ofReal_mul]
  field_simp [hs3]
  norm_num

private lemma hasDerivAt_one_add_div_three :
    HasDerivAt (fun z : ℂ => 1 + z / 3) (1 / 3 : ℂ) (1 : ℂ) := by
  have hid : HasDerivAt (fun z : ℂ => z) 1 (1 : ℂ) := by
    simpa using hasDerivAt_id (1 : ℂ)
  have h := (hasDerivAt_const (1 : ℂ) (1 : ℂ)).add (hid.div_const (3 : ℂ))
  simpa only [Pi.add_apply, zero_add] using h

private lemma hasDerivAt_one_sub :
    HasDerivAt (fun z : ℂ => 1 - z) (-1 : ℂ) (1 : ℂ) := by
  have hid : HasDerivAt (fun z : ℂ => z) 1 (1 : ℂ) := by
    simpa using hasDerivAt_id (1 : ℂ)
  have h := (hasDerivAt_const (1 : ℂ) (1 : ℂ)).sub hid
  simpa only [Pi.sub_apply, zero_sub] using h

lemma riordanSecondNoS_one :
    riordanSecondNoS (1 : ℂ) = 0 := by
  unfold riordanSecondNoS riordanAnalyticLinearCoeff riordanSecondSingularCoeff
  rw [riordanSqrtPlus_one]
  unfold riordanSqrtPlusAtOneℂ riordanSingularCoeff riordanAℂ
  have hs3 : ((Real.sqrt 3 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 3))
  norm_num [Complex.ofReal_div, Complex.ofReal_mul]
  field_simp [hs3]
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

lemma riordanSecondSqrtCoeff_one :
    riordanSecondSqrtCoeff (1 : ℂ) = 0 := by
  unfold riordanSecondSqrtCoeff riordanAnalyticLinearCoeff riordanSecondSingularCoeff
  rw [riordanSqrtPlus_one]
  unfold riordanSqrtPlusAtOneℂ riordanSingularCoeff riordanAℂ
  have hs3 : ((Real.sqrt 3 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 3))
  norm_num [Complex.ofReal_div, Complex.ofReal_mul]
  field_simp [hs3]
  norm_num

lemma hasDerivAt_riordanSecondNoS_one :
    HasDerivAt riordanSecondNoS 0 (1 : ℂ) := by
  have h1 := HasDerivAt.const_mul (-2 : ℂ) hasDerivAt_riordanSqrtPlus_one
  have h2 := HasDerivAt.const_mul (riordanSingularCoeff * riordanAℂ)
    hasDerivAt_one_add_div_three
  have h3 := HasDerivAt.const_mul (riordanAℂ * riordanSecondSingularCoeff)
    (hasDerivAt_one_sub.mul hasDerivAt_one_add_div_three)
  have h4 := HasDerivAt.const_mul (riordanAℂ * riordanAnalyticLinearCoeff)
    (hasDerivAt_riordanSqrtPlus_one.mul hasDerivAt_one_sub)
  have hcalc := ((h1.sub h2).sub h3).sub h4
  convert hcalc using 1
  · ext z
    simp [riordanSecondNoS]
    ring
  · rw [riordanSqrtPlus_one]
    unfold riordanSqrtPlusAtOneℂ riordanAnalyticLinearCoeff
      riordanSecondSingularCoeff riordanSingularCoeff riordanAℂ
    have hs3 : ((Real.sqrt 3 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 3))
    norm_num [Complex.ofReal_div, Complex.ofReal_mul]
    field_simp [hs3]
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num

lemma hasDerivAt_riordanSecondSqrtCoeff_one :
    HasDerivAt riordanSecondSqrtCoeff (-(8 / 3 : ℂ)) (1 : ℂ) := by
  have h0 : HasDerivAt (fun _ : ℂ => (2 / 3 : ℂ)) 0 (1 : ℂ) :=
    hasDerivAt_const (1 : ℂ) _
  have h1 := HasDerivAt.const_mul (riordanSingularCoeff * riordanAℂ)
    hasDerivAt_riordanSqrtPlus_one
  have h2 := HasDerivAt.const_mul (riordanAℂ * riordanAnalyticLinearCoeff)
    hasDerivAt_one_add_div_three
  have h3 := HasDerivAt.const_mul (riordanAℂ * riordanSecondSingularCoeff)
    (hasDerivAt_one_sub.mul hasDerivAt_riordanSqrtPlus_one)
  have hcalc := ((h0.sub h1).sub h2).sub h3
  convert hcalc using 1
  · ext z
    simp [riordanSecondSqrtCoeff]
    ring
  · rw [riordanSqrtPlus_one]
    unfold riordanSqrtPlusAtOneℂ riordanAnalyticLinearCoeff
      riordanSecondSingularCoeff riordanSingularCoeff riordanAℂ
    have hs3 : ((Real.sqrt 3 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 3))
    norm_num [Complex.ofReal_div, Complex.ofReal_mul]
    field_simp [hs3]
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num

private lemma nhdsWithin_riordan_delta_le_punctured :
    𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ) ≤
      𝓝[({1}ᶜ : Set ℂ)] (1 : ℂ) := by
  exact nhdsWithin_mono _ (by intro z hz; exact hz.2.1)

lemma tendsto_riordanSecondNoS_div :
    Tendsto (fun z : ℂ => riordanSecondNoS z / (1 - z))
      (𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)) (𝓝 0) := by
  let l := 𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)
  have hslope : Tendsto (slope riordanSecondNoS (1 : ℂ)) l (𝓝 (0 : ℂ)) :=
    hasDerivAt_riordanSecondNoS_one.tendsto_slope.mono_left
      nhdsWithin_riordan_delta_le_punctured
  have hneg : Tendsto (fun z : ℂ => -slope riordanSecondNoS (1 : ℂ) z) l
      (𝓝 (0 : ℂ)) := by
    simpa using hslope.neg
  refine hneg.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz_ne : z ≠ 1 := hz.2.1
  have h1z : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz_ne)
  have hz1 : z - (1 : ℂ) ≠ 0 := sub_ne_zero.mpr hz_ne
  simp [slope, riordanSecondNoS_one, div_eq_mul_inv]
  field_simp [h1z, hz1]
  ring

lemma tendsto_riordanSecondSqrtCoeff_div :
    Tendsto (fun z : ℂ => riordanSecondSqrtCoeff z / (1 - z))
      (𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)) (𝓝 (8 / 3 : ℂ)) := by
  let l := 𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)
  have hslope : Tendsto (slope riordanSecondSqrtCoeff (1 : ℂ)) l (𝓝 (-(8 / 3 : ℂ))) :=
    hasDerivAt_riordanSecondSqrtCoeff_one.tendsto_slope.mono_left
      nhdsWithin_riordan_delta_le_punctured
  have hneg : Tendsto (fun z : ℂ => -slope riordanSecondSqrtCoeff (1 : ℂ) z) l
      (𝓝 (8 / 3 : ℂ)) := by
    simpa using hslope.neg
  refine hneg.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz_ne : z ≠ 1 := hz.2.1
  have h1z : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz_ne)
  have hz1 : z - (1 : ℂ) ≠ 0 := sub_ne_zero.mpr hz_ne
  simp [slope, riordanSecondSqrtCoeff_one, div_eq_mul_inv]
  field_simp [h1z, hz1]
  ring

lemma riordanSecondQuotient_decomp {z : ℂ} (hznorm : ‖z‖ < 3) :
    riordanSingularityQuotientModel z -
        riordanAnalyticLinearCoeff * riordanSqrtOneSub z -
        riordanSecondSingularCoeff * (1 - z) =
      (riordanSecondNoS z +
          riordanSqrtOneSub z * riordanSecondSqrtCoeff z) /
        (riordanAℂ * riordanRescaledDenominator z) := by
  set s := riordanSqrtOneSub z with hs_def
  set t := riordanSqrtPlus z with ht_def
  have hs_sq : s ^ 2 = 1 - z := by
    rw [hs_def]
    exact riordanSqrtOneSub_sq z
  have hdD : riordanRescaledDenominator z ≠ 0 :=
    riordanRescaledDenominator_ne_zero_of_norm_lt_three hznorm
  have hd : riordanAℂ * riordanRescaledDenominator z ≠ 0 := by
    exact mul_ne_zero (by norm_num [riordanAℂ]) hdD
  have hd' : riordanAℂ * (1 + z / 3 + t * s) ≠ 0 := by
    rw [hs_def, ht_def]
    simpa [riordanRescaledDenominator] using hd
  unfold riordanSingularityQuotientModel riordanSecondNoS
    riordanSecondSqrtCoeff riordanAnalyticLinearCoeff
    riordanSecondSingularCoeff riordanRescaledDenominator
  rw [← hs_def, ← ht_def]
  rw [eq_div_iff hd']
  rw [sub_mul, sub_mul]
  rw [div_mul_cancel₀ _ hd']
  rw [← hs_sq]
  ring

lemma riordanSecondQuotient_div_eq {z : ℂ} (hz : z ≠ 1) (hznorm : ‖z‖ < 3) :
    (riordanSingularityQuotientModel z -
        riordanAnalyticLinearCoeff * riordanSqrtOneSub z -
        riordanSecondSingularCoeff * (1 - z)) / (1 - z) =
      (riordanSecondNoS z / (1 - z) +
          riordanSqrtOneSub z * (riordanSecondSqrtCoeff z / (1 - z))) /
        (riordanAℂ * riordanRescaledDenominator z) := by
  rw [riordanSecondQuotient_decomp hznorm]
  have h1z : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  have hD : riordanRescaledDenominator z ≠ 0 :=
    riordanRescaledDenominator_ne_zero_of_norm_lt_three hznorm
  have hAD : riordanAℂ * riordanRescaledDenominator z ≠ 0 :=
    mul_ne_zero (by norm_num [riordanAℂ]) hD
  field_simp [h1z, hAD]

lemma tendsto_riordanSecondQuotient_div :
    Tendsto
      (fun z : ℂ =>
        (riordanSingularityQuotientModel z -
          riordanAnalyticLinearCoeff * riordanSqrtOneSub z -
          riordanSecondSingularCoeff * (1 - z)) / (1 - z))
      (𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)) (𝓝 0) := by
  let l := 𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)
  have hnum : Tendsto
      (fun z : ℂ =>
        riordanSecondNoS z / (1 - z) +
          riordanSqrtOneSub z * (riordanSecondSqrtCoeff z / (1 - z))) l
      (𝓝 (0 + 0 * (8 / 3 : ℂ))) := by
    exact tendsto_riordanSecondNoS_div.add
      (tendsto_riordanSqrtOneSub.mul tendsto_riordanSecondSqrtCoeff_div)
  have hden : Tendsto
      (fun z : ℂ => riordanAℂ * riordanRescaledDenominator z) l
      (𝓝 (riordanAℂ * riordanAℂ)) := by
    exact tendsto_const_nhds.mul tendsto_riordanRescaledDenominator
  have hden_ne : riordanAℂ * riordanAℂ ≠ 0 := by
    norm_num [riordanAℂ]
  have hquot := hnum.div hden hden_ne
  have hquot0 : Tendsto
      (fun z : ℂ =>
        (riordanSecondNoS z / (1 - z) +
            riordanSqrtOneSub z * (riordanSecondSqrtCoeff z / (1 - z))) /
          (riordanAℂ * riordanRescaledDenominator z)) l (𝓝 0) := by
    convert hquot using 1
    norm_num
  refine hquot0.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (riordanSecondQuotient_div_eq hz.2.1 (by nlinarith [hz.1])).symm

lemma tendsto_riordanSecondQuotient_twoTerm :
    Tendsto
      (fun z : ℂ =>
        ‖riordanSingularityQuotientModel z -
            riordanAnalyticLinearCoeff * riordanSqrtOneSub z -
            riordanSecondSingularCoeff * (1 - z)‖ *
          ‖(1 : ℂ) - z‖ ^ (-(1 : ℝ)))
      (𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)) (𝓝 0) := by
  let l := 𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)
  have hnorm : Tendsto
      (fun z : ℂ =>
        ‖(riordanSingularityQuotientModel z -
          riordanAnalyticLinearCoeff * riordanSqrtOneSub z -
          riordanSecondSingularCoeff * (1 - z)) / (1 - z)‖) l (𝓝 0) := by
    simpa using tendsto_riordanSecondQuotient_div.norm
  refine hnorm.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz_ne : z ≠ 1 := hz.2.1
  have h1z : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz_ne)
  rw [Real.rpow_neg (norm_nonneg ((1 : ℂ) - z)), Real.rpow_one]
  rw [show
      ‖riordanSingularityQuotientModel z -
          riordanAnalyticLinearCoeff * riordanSqrtOneSub z -
          riordanSecondSingularCoeff * (1 - z)‖ * ‖(1 : ℂ) - z‖⁻¹ =
        ‖riordanSingularityQuotientModel z -
          riordanAnalyticLinearCoeff * riordanSqrtOneSub z -
          riordanSecondSingularCoeff * (1 - z)‖ / ‖(1 : ℂ) - z‖ by
        rw [div_eq_mul_inv]]
  rw [← norm_div]

lemma riordan_adjusted_residual_eq {z : ℂ} (hz : z ≠ 1) (hznorm : ‖z‖ < 3) :
    riordanAdjustedRescaledFun z -
        riordanSingularCoeff * (1 - z) ^ (1 / 2 : ℂ) -
        riordanSecondSingularCoeff * (1 - z) ^ (3 / 2 : ℂ) =
      riordanSqrtOneSub z *
        (riordanSingularityQuotientModel z -
          riordanAnalyticLinearCoeff * riordanSqrtOneSub z -
          riordanSecondSingularCoeff * (1 - z)) := by
  let s := riordanSqrtOneSub z
  have hs_ne : s ≠ 0 := by
    dsimp [s]
    exact riordanSqrtOneSub_ne_zero_of_ne_one hz
  have hQ := riordan_singularity_quotient_eq hz hznorm
  have hcenter : riordanCenteredRescaledFun z - riordanSingularCoeff * s =
      riordanSingularityQuotientModel z * s := by
    have hmul := congrArg (fun w : ℂ => w * s) hQ
    dsimp [s] at hmul ⊢
    rw [div_mul_cancel₀ _ hs_ne] at hmul
    exact hmul
  have hs_sq : s ^ 2 = 1 - z := by
    dsimp [s]
    exact riordanSqrtOneSub_sq z
  have hu_ne : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  have hpow_three_halves : (1 - z) ^ (3 / 2 : ℂ) = (1 - z) * s := by
    dsimp [s]
    rw [show (3 / 2 : ℂ) = 1 + (1 / 2 : ℂ) by norm_num]
    rw [Complex.cpow_add _ _ hu_ne, Complex.cpow_one]
    rfl
  unfold riordanAdjustedRescaledFun
  change riordanCenteredRescaledFun z - riordanAnalyticLinearCoeff * (1 - z) -
      riordanSingularCoeff * riordanSqrtOneSub z -
      riordanSecondSingularCoeff * (1 - z) ^ (3 / 2 : ℂ) =
    riordanSqrtOneSub z *
      (riordanSingularityQuotientModel z -
        riordanAnalyticLinearCoeff * riordanSqrtOneSub z -
        riordanSecondSingularCoeff * (1 - z))
  rw [hpow_three_halves]
  rw [show riordanCenteredRescaledFun z - riordanAnalyticLinearCoeff * (1 - z) -
      riordanSingularCoeff * riordanSqrtOneSub z -
      riordanSecondSingularCoeff * ((1 - z) * riordanSqrtOneSub z) =
      (riordanCenteredRescaledFun z - riordanSingularCoeff * riordanSqrtOneSub z) -
        riordanAnalyticLinearCoeff * (1 - z) -
        riordanSecondSingularCoeff * ((1 - z) * riordanSqrtOneSub z) by ring]
  dsimp [s] at hcenter hs_sq
  rw [hcenter]
  rw [← hs_sq]
  ring

lemma riordan_adjusted_singularity_twoTerm_norm_eq {z : ℂ}
    (hz : z ≠ 1) (hznorm : ‖z‖ < 3) :
    ‖riordanAdjustedRescaledFun z -
        riordanSingularCoeff * (1 - z) ^ (1 / 2 : ℂ) -
        riordanSecondSingularCoeff * (1 - z) ^ (3 / 2 : ℂ)‖ *
      ‖(1 : ℂ) - z‖ ^ (-(3 / 2 : ℝ)) =
    ‖riordanSingularityQuotientModel z -
        riordanAnalyticLinearCoeff * riordanSqrtOneSub z -
        riordanSecondSingularCoeff * (1 - z)‖ *
      ‖(1 : ℂ) - z‖ ^ (-(1 : ℝ)) := by
  let u : ℂ := 1 - z
  have hu_ne : u ≠ 0 := by
    dsimp [u]
    exact sub_ne_zero.mpr (Ne.symm hz)
  have hu_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu_ne
  have hs_norm : ‖riordanSqrtOneSub z‖ = ‖u‖ ^ (1 / 2 : ℝ) := by
    dsimp [u]
    unfold riordanSqrtOneSub motzkinSqrtOneSub
    convert Complex.norm_cpow_real ((1 : ℂ) - z) (1 / 2 : ℝ) using 1
    norm_num
  rw [riordan_adjusted_residual_eq hz hznorm]
  rw [norm_mul, hs_norm]
  change (‖u‖ ^ (1 / 2 : ℝ) *
        ‖riordanSingularityQuotientModel z -
          riordanAnalyticLinearCoeff * riordanSqrtOneSub z -
          riordanSecondSingularCoeff * (1 - z)‖) *
      ‖u‖ ^ (-(3 / 2 : ℝ)) =
    ‖riordanSingularityQuotientModel z -
        riordanAnalyticLinearCoeff * riordanSqrtOneSub z -
        riordanSecondSingularCoeff * (1 - z)‖ *
      ‖u‖ ^ (-(1 : ℝ))
  have hpow : ‖u‖ ^ (1 / 2 : ℝ) * ‖u‖ ^ (-(3 / 2 : ℝ)) =
      ‖u‖ ^ (-(1 : ℝ)) := by
    rw [← Real.rpow_add hu_pos]
    norm_num
  rw [show ‖u‖ ^ (1 / 2 : ℝ) *
        ‖riordanSingularityQuotientModel z -
          riordanAnalyticLinearCoeff * riordanSqrtOneSub z -
          riordanSecondSingularCoeff * (1 - z)‖ * ‖u‖ ^ (-(3 / 2 : ℝ)) =
      ‖riordanSingularityQuotientModel z -
          riordanAnalyticLinearCoeff * riordanSqrtOneSub z -
          riordanSecondSingularCoeff * (1 - z)‖ *
        (‖u‖ ^ (1 / 2 : ℝ) * ‖u‖ ^ (-(3 / 2 : ℝ))) by ring, hpow]

lemma riordanAdjustedRescaledFun_singularity_twoTerm :
    Tendsto
      (fun z : ℂ =>
        ‖riordanAdjustedRescaledFun z -
            riordanSingularCoeff * (1 - z) ^ (1 / 2 : ℂ) -
            riordanSecondSingularCoeff * (1 - z) ^ (3 / 2 : ℂ)‖ *
          ‖(1 : ℂ) - z‖ ^ (-(3 / 2 : ℝ)))
      (𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)) (𝓝 0) := by
  refine tendsto_riordanSecondQuotient_twoTerm.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (riordan_adjusted_singularity_twoTerm_norm_eq hz.2.1 (by nlinarith [hz.1])).symm

lemma riordan_neg_half_pole :
    ∀ m : ℕ, (-(1 / 2 : ℝ)) ≠ 1 - (m : ℝ) := by
  intro m h
  have hm2R : (2 * m : ℝ) = 3 := by nlinarith
  have hm2N : 2 * m = 3 := by exact_mod_cast hm2R
  omega

lemma riordan_Real_Gamma_neg_half :
    Real.Gamma (-(1 / 2 : ℝ)) = -2 * Real.sqrt Real.pi := by
  have h := Real.Gamma_add_one (s := (-(1 / 2 : ℝ)))
    (by norm_num : (-(1 / 2 : ℝ)) ≠ 0)
  norm_num at h
  rw [Real.Gamma_one_half_eq] at h
  linarith

lemma riordan_Real_Gamma_neg_three_halves :
    Real.Gamma (-(3 / 2 : ℝ)) = 4 * Real.sqrt Real.pi / 3 := by
  have h := Real.Gamma_add_one (s := (-(3 / 2 : ℝ)))
    (by norm_num : (-(3 / 2 : ℝ)) ≠ 0)
  norm_num at h
  rw [riordan_Real_Gamma_neg_half] at h
  nlinarith

lemma riordan_secondOrder_model_complex_eq (n : ℕ) :
    (riordanSingularCoeff *
        ((((n : ℝ) ^ ((-(1 / 2 : ℝ)) - 1) /
              Real.Gamma (-(1 / 2 : ℝ)) : ℝ) : ℂ) +
          ((((-(1 / 2 : ℝ)) * ((-(1 / 2 : ℝ)) - 1) / 2 /
                Real.Gamma (-(1 / 2 : ℝ))) *
              (n : ℝ) ^ ((-(1 / 2 : ℝ)) - 2) : ℝ) : ℂ)) +
      riordanSecondSingularCoeff *
        (((n : ℝ) ^ ((-(1 / 2 : ℝ)) - 2) /
          Real.Gamma ((-(1 / 2 : ℝ)) - 1) : ℝ) : ℂ)) =
      (((riordanAsymptoticConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
          riordanSecondAsymptoticConstant * (n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ)) := by
  have hpow1 : (n : ℝ) ^ ((-(1 / 2 : ℝ)) - 1) =
      (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
    congr 1
    norm_num
  have hpow2 : (n : ℝ) ^ ((-(1 / 2 : ℝ)) - 2) =
      (n : ℝ) ^ (-(5 / 2 : ℝ)) := by
    congr 1
    norm_num
  rw [hpow1, hpow2]
  unfold riordanSecondSingularCoeff riordanSingularCoeff
    riordanAsymptoticConstant riordanSecondAsymptoticConstant
  rw [riordan_Real_Gamma_neg_half,
    show (-(1 / 2 : ℝ)) - 1 = -(3 / 2 : ℝ) by norm_num,
    riordan_Real_Gamma_neg_three_halves]
  norm_num [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_neg]
  ring

theorem riordanAdjustedRescaledCoeff_secondOrder_of_singularity
    (hsing : Tendsto
      (fun z : ℂ =>
        ‖riordanAdjustedRescaledFun z -
            riordanSingularCoeff * (1 - z) ^ (1 / 2 : ℂ) -
            riordanSecondSingularCoeff * (1 - z) ^ (3 / 2 : ℂ)‖ *
          ‖(1 : ℂ) - z‖ ^ (-(3 / 2 : ℝ)))
      (𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)) (𝓝 0)) :
    (fun n : ℕ =>
      riordanAdjustedRescaledFMLS.coeff n -
        (((riordanAsymptoticConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
            riordanSecondAsymptoticConstant * (n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ)))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(5 / 2 : ℝ))) := by
  have htransfer := transfer_twoTerm_secondOrder_general
    (α := (-(1 / 2 : ℝ))) (C0 := riordanSingularCoeff)
    (C1 := riordanSecondSingularCoeff)
    (R := (3 / 2 : ℝ)) (φ := Real.pi / 4)
    (f := riordanAdjustedRescaledFun) (p := riordanAdjustedRescaledFMLS)
    riordan_neg_half_pole (by norm_num) (by positivity) ?_
    riordanAdjustedRescaledFun_hasFPowerSeriesAt_zero
    analyticOnNhd_riordanAdjustedRescaledFun ?_
  · have hcomplex :
        (fun n : ℕ =>
          riordanAdjustedRescaledFMLS.coeff n -
            (((riordanAsymptoticConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
                riordanSecondAsymptoticConstant * (n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ)))
          =o[atTop] (fun n : ℕ => (n : ℝ) ^ ((-(1 / 2 : ℝ)) - 2)) := by
      refine htransfer.congr_left ?_
      intro n
      rw [riordan_secondOrder_model_complex_eq n]
    convert hcomplex using 1
    ext n
    congr 1
    norm_num
  · nlinarith [Real.pi_pos]
  · convert hsing using 1
    ext z
    norm_num

theorem riordanCenteredRescaledCoeff_secondOrder_of_singularity
    (hsing : Tendsto
      (fun z : ℂ =>
        ‖riordanAdjustedRescaledFun z -
            riordanSingularCoeff * (1 - z) ^ (1 / 2 : ℂ) -
            riordanSecondSingularCoeff * (1 - z) ^ (3 / 2 : ℂ)‖ *
          ‖(1 : ℂ) - z‖ ^ (-(3 / 2 : ℝ)))
      (𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)) (𝓝 0)) :
    (fun n : ℕ =>
      (PowerSeries.toFMLS riordanCenteredRescaledSeriesℂ).coeff n -
        (((riordanAsymptoticConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
            riordanSecondAsymptoticConstant * (n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ)))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(5 / 2 : ℝ))) := by
  have h := riordanAdjustedRescaledCoeff_secondOrder_of_singularity hsing
  refine h.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_ge_atTop 2] with n hn
  rw [coeff_riordanAdjustedRescaledFMLS_of_two_le hn]

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

theorem riordanRescaled_complex_secondOrder_of_singularity
    (hsing : Tendsto
      (fun z : ℂ =>
        ‖riordanAdjustedRescaledFun z -
            riordanSingularCoeff * (1 - z) ^ (1 / 2 : ℂ) -
            riordanSecondSingularCoeff * (1 - z) ^ (3 / 2 : ℂ)‖ *
          ‖(1 : ℂ) - z‖ ^ (-(3 / 2 : ℝ)))
      (𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)) (𝓝 0)) :
    (fun n : ℕ =>
      (riordan n : ℂ) * ((3 : ℂ)⁻¹) ^ n -
        (((riordanAsymptoticConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
            riordanSecondAsymptoticConstant * (n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ)))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(5 / 2 : ℝ))) := by
  have hcenter := riordanCenteredRescaledCoeff_secondOrder_of_singularity hsing
  refine hcenter.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_ne_atTop 0] with n hn
  rw [PowerSeries.coeff_toFMLS, coeff_riordanCenteredRescaledSeriesℂ_of_ne_zero hn,
    coeff_riordanRescaledSeriesℂ]

lemma riordanSecondAsymptoticConstant_eq_relative :
    riordanSecondAsymptoticConstant =
      riordanAsymptoticConstant * riordanRelativeSecondConstant := by
  unfold riordanSecondAsymptoticConstant riordanAsymptoticConstant
    riordanRelativeSecondConstant
  ring

theorem riordanAdjustedRescaledCoeff_secondOrder :
    (fun n : ℕ =>
      riordanAdjustedRescaledFMLS.coeff n -
        (((riordanAsymptoticConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
            riordanSecondAsymptoticConstant * (n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ)))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(5 / 2 : ℝ))) :=
  riordanAdjustedRescaledCoeff_secondOrder_of_singularity
    riordanAdjustedRescaledFun_singularity_twoTerm

theorem riordanCenteredRescaledCoeff_secondOrder :
    (fun n : ℕ =>
      (PowerSeries.toFMLS riordanCenteredRescaledSeriesℂ).coeff n -
        (((riordanAsymptoticConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
            riordanSecondAsymptoticConstant * (n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ)))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(5 / 2 : ℝ))) :=
  riordanCenteredRescaledCoeff_secondOrder_of_singularity
    riordanAdjustedRescaledFun_singularity_twoTerm

theorem riordanRescaled_complex_secondOrder :
    (fun n : ℕ =>
      (riordan n : ℂ) * ((3 : ℂ)⁻¹) ^ n -
        (((riordanAsymptoticConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
            riordanSecondAsymptoticConstant * (n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ)))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(5 / 2 : ℝ))) :=
  riordanRescaled_complex_secondOrder_of_singularity
    riordanAdjustedRescaledFun_singularity_twoTerm

theorem riordanRescaled_secondOrder :
    (fun n : ℕ =>
      (riordan n : ℝ) * ((3 : ℝ)⁻¹) ^ n -
        (riordanAsymptoticConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
          riordanSecondAsymptoticConstant * (n : ℝ) ^ (-(5 / 2 : ℝ))))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(5 / 2 : ℝ))) := by
  have hcomplex :
      (fun n : ℕ =>
        (((riordan n : ℝ) * ((3 : ℝ)⁻¹) ^ n : ℝ) : ℂ) -
          (((riordanAsymptoticConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
              riordanSecondAsymptoticConstant * (n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ)))
        =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(5 / 2 : ℝ))) := by
    refine riordanRescaled_complex_secondOrder.congr_left ?_
    intro n
    have hpow : ((3 : ℂ)⁻¹) ^ n = ((((3 : ℝ)⁻¹) ^ n : ℝ) : ℂ) := by
      have hbase : (3 : ℂ)⁻¹ = (((3 : ℝ)⁻¹ : ℝ) : ℂ) := by
        rw [Complex.ofReal_inv]
        norm_num
      rw [hbase, Complex.ofReal_pow]
    have hcoeff :
        (riordan n : ℂ) * ((3 : ℂ)⁻¹) ^ n =
          (((riordan n : ℝ) * ((3 : ℝ)⁻¹) ^ n : ℝ) : ℂ) := by
      rw [hpow]
      norm_num [Complex.ofReal_mul]
    rw [hcoeff]
  have hreal := complex_re_isLittleO_ofReal hcomplex
  refine hreal.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards with n
  rw [Complex.ofReal_re]

theorem riordan_secondOrder_additive :
    (fun n : ℕ =>
      (riordan n : ℝ) -
        (3 : ℝ) ^ n *
          (riordanAsymptoticConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
            riordanSecondAsymptoticConstant * (n : ℝ) ^ (-(5 / 2 : ℝ))))
      =o[atTop]
        (fun n : ℕ => (3 : ℝ) ^ n * (n : ℝ) ^ (-(5 / 2 : ℝ))) := by
  have hmul := riordanRescaled_secondOrder.mul_isBigO
    (isBigO_refl (fun n : ℕ => (3 : ℝ) ^ n) atTop)
  refine hmul.congr' ?_ ?_
  · filter_upwards with n
    have h3 : (3 : ℝ) ≠ 0 := by norm_num
    calc
      ((riordan n : ℝ) * ((3 : ℝ)⁻¹) ^ n -
          (riordanAsymptoticConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
            riordanSecondAsymptoticConstant * (n : ℝ) ^ (-(5 / 2 : ℝ)))) *
          (3 : ℝ) ^ n
          = (riordan n : ℝ) * (((3 : ℝ)⁻¹) ^ n * (3 : ℝ) ^ n) -
              (3 : ℝ) ^ n *
                (riordanAsymptoticConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
                  riordanSecondAsymptoticConstant * (n : ℝ) ^ (-(5 / 2 : ℝ))) := by
            ring
      _ = (riordan n : ℝ) -
              (3 : ℝ) ^ n *
                (riordanAsymptoticConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
                  riordanSecondAsymptoticConstant * (n : ℝ) ^ (-(5 / 2 : ℝ))) := by
            rw [← mul_pow, inv_mul_cancel₀ h3, one_pow, mul_one]
  · filter_upwards with n
    ring

theorem riordan_secondOrder :
    (fun n : ℕ =>
      (riordan n : ℝ) -
        (3 : ℝ) ^ n * riordanAsymptoticConstant *
          (n : ℝ) ^ (-(3 / 2 : ℝ)) *
          (1 + riordanRelativeSecondConstant * (n : ℝ) ^ (-(1 : ℝ))))
      =o[atTop]
        (fun n : ℕ => (3 : ℝ) ^ n * (n : ℝ) ^ (-(5 / 2 : ℝ))) := by
  refine riordan_secondOrder_additive.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ)) hn)
  have hpow : (n : ℝ) ^ (-(5 / 2 : ℝ)) =
      (n : ℝ) ^ (-(3 / 2 : ℝ)) * (n : ℝ) ^ (-(1 : ℝ)) := by
    rw [← Real.rpow_add hnpos]
    norm_num
  rw [riordanSecondAsymptoticConstant_eq_relative, hpow]
  ring

end
