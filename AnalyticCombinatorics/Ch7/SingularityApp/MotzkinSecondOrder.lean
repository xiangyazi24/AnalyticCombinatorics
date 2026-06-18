import AnalyticCombinatorics.Ch4.Analytic.TransferSecondOrderGeneral
import AnalyticCombinatorics.Ch7.SingularityApp.Motzkin

/-!
# Second-order Motzkin asymptotics

The centered rescaled Motzkin function has an analytic linear term between the
two half-integer singular terms.  We subtract that linear term before applying
the general second-order transfer theorem; its coefficients vanish for `n ≥ 2`.
-/

set_option maxHeartbeats 1200000

open Complex Filter Asymptotics Set
open scoped Topology BigOperators PowerSeries

noncomputable section

def motzkinAnalyticLinearCoeff : ℂ := (15 / 2 : ℂ)

def motzkinSecondSingularCoeff : ℂ :=
  -(((45 * Real.sqrt 3 / 8 : ℝ) : ℂ))

def motzkinRelativeSecondConstant : ℝ := -(39 / 16 : ℝ)

def motzkinSecondAsymptoticConstant : ℝ :=
  -(117 * Real.sqrt 3 / (32 * Real.sqrt Real.pi))

def motzkinOneSubSeriesℂ : PowerSeries ℂ :=
  (1 : PowerSeries ℂ) - PowerSeries.X

def motzkinAdjustedRescaledFMLS : FormalMultilinearSeries ℂ ℂ ℂ :=
  PowerSeries.toFMLS motzkinCenteredRescaledSeriesℂ -
    motzkinAnalyticLinearCoeff • PowerSeries.toFMLS motzkinOneSubSeriesℂ

def motzkinAdjustedRescaledFun (z : ℂ) : ℂ :=
  motzkinCenteredRescaledFun z - motzkinAnalyticLinearCoeff * (1 - z)

private lemma coeff_sub_const_smul (C : ℂ)
    (p q : FormalMultilinearSeries ℂ ℂ ℂ) (n : ℕ) :
    (p - C • q).coeff n = p.coeff n - C * q.coeff n := by
  change (p n - (C • q) n) 1 = p n 1 - C * q.coeff n
  rw [FormalMultilinearSeries.smul_apply]
  rw [ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.smul_apply]
  change p.coeff n - C • q.coeff n = p.coeff n - C * q.coeff n
  simp [smul_eq_mul]

lemma coeff_motzkinOneSubSeriesℂ_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    (PowerSeries.toFMLS motzkinOneSubSeriesℂ).coeff n = 0 := by
  rw [PowerSeries.coeff_toFMLS]
  simp [motzkinOneSubSeriesℂ, PowerSeries.coeff_X, PowerSeries.coeff_one,
    ne_of_gt (lt_of_lt_of_le (by norm_num : 0 < 2) hn),
    ne_of_gt (lt_of_lt_of_le (by norm_num : 1 < 2) hn)]

lemma coeff_motzkinAdjustedRescaledFMLS_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    motzkinAdjustedRescaledFMLS.coeff n =
      (PowerSeries.toFMLS motzkinCenteredRescaledSeriesℂ).coeff n := by
  rw [motzkinAdjustedRescaledFMLS, coeff_sub_const_smul,
    coeff_motzkinOneSubSeriesℂ_of_two_le hn]
  ring

lemma hasFPowerSeriesAt_one_sub_toFMLS :
    HasFPowerSeriesAt (fun z : ℂ => 1 - z)
      (PowerSeries.toFMLS motzkinOneSubSeriesℂ) (0 : ℂ) := by
  have hconst := hasFPowerSeriesAt_const_toFMLS_C (1 : ℂ)
  have hid := hasFPowerSeriesAt_id_toFMLS_X
  have hsub := hconst.sub hid
  simpa [motzkinOneSubSeriesℂ, toFMLS_sub] using hsub

theorem motzkinAdjustedRescaledFun_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt motzkinAdjustedRescaledFun
      motzkinAdjustedRescaledFMLS (0 : ℂ) := by
  have hlin := hasFPowerSeriesAt_one_sub_toFMLS.const_smul
    (c := motzkinAnalyticLinearCoeff)
  have hsub := motzkinCenteredRescaledFun_hasFPowerSeriesAt_zero.sub hlin
  simpa [motzkinAdjustedRescaledFun, motzkinAdjustedRescaledFMLS, smul_eq_mul] using hsub

lemma analyticOnNhd_motzkinAdjustedRescaledFun :
    AnalyticOnNhd ℂ motzkinAdjustedRescaledFun
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
  have hlinear : AnalyticOnNhd ℂ (fun z : ℂ => motzkinAnalyticLinearCoeff * (1 - z))
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
    simpa [smul_eq_mul] using
      (analyticOnNhd_const.mul
        ((analyticOnNhd_const.sub analyticOnNhd_id)))
  simpa [motzkinAdjustedRescaledFun] using
    analyticOnNhd_motzkinCenteredRescaledFun.sub hlinear

def motzkinSecondNoS (z : ℂ) : ℂ :=
  3 * motzkinSqrtThreeℂ * (1 - z / 3) - 3 * motzkinSqrtPlus z -
    motzkinAnalyticLinearCoeff * motzkinSqrtPlus z * (1 - z) -
    motzkinSecondSingularCoeff * (1 - z) * (1 - z / 3)

def motzkinSecondSqrtCoeff (z : ℂ) : ℂ :=
  -1 + 3 * motzkinSqrtThreeℂ * motzkinSqrtPlus z -
    motzkinAnalyticLinearCoeff * (1 - z / 3) -
    motzkinSecondSingularCoeff * motzkinSqrtPlus z * (1 - z)

lemma motzkinSqrtPlus_one :
    motzkinSqrtPlus (1 : ℂ) = ((2 / Real.sqrt 3 : ℝ) : ℂ) := by
  unfold motzkinSqrtPlus
  rw [show (1 : ℂ) + 1 / 3 = ((4 / 3 : ℝ) : ℂ) by norm_num]
  exact Complex_cpow_four_thirds_half

lemma hasDerivAt_motzkinSqrtPlus_one :
    HasDerivAt motzkinSqrtPlus (((Real.sqrt 3 / 12 : ℝ) : ℂ)) (1 : ℂ) := by
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

lemma motzkinSecondNoS_one :
    motzkinSecondNoS (1 : ℂ) = 0 := by
  unfold motzkinSecondNoS motzkinAnalyticLinearCoeff motzkinSecondSingularCoeff
  rw [motzkinSqrtPlus_one]
  have hs3 : ((Real.sqrt 3 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 3))
  unfold motzkinSqrtThreeℂ
  norm_num [Complex.ofReal_div, Complex.ofReal_mul]
  field_simp [hs3]
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

lemma motzkinSecondSqrtCoeff_one :
    motzkinSecondSqrtCoeff (1 : ℂ) = 0 := by
  unfold motzkinSecondSqrtCoeff motzkinAnalyticLinearCoeff motzkinSecondSingularCoeff
  rw [motzkinSqrtPlus_one]
  have hs3 : ((Real.sqrt 3 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 3))
  unfold motzkinSqrtThreeℂ
  norm_num [Complex.ofReal_div, Complex.ofReal_mul]
  field_simp [hs3]
  norm_num

private lemma hasDerivAt_one_sub_div_three :
    HasDerivAt (fun z : ℂ => 1 - z / 3) (-(1 / 3 : ℂ)) (1 : ℂ) := by
  have hid : HasDerivAt (fun z : ℂ => z) 1 (1 : ℂ) := by
    simpa using hasDerivAt_id (1 : ℂ)
  have h := (hasDerivAt_const (1 : ℂ) (1 : ℂ)).sub (hid.div_const (3 : ℂ))
  simpa only [Pi.sub_apply, zero_sub] using h

private lemma hasDerivAt_one_sub :
    HasDerivAt (fun z : ℂ => 1 - z) (-1 : ℂ) (1 : ℂ) := by
  have hid : HasDerivAt (fun z : ℂ => z) 1 (1 : ℂ) := by
    simpa using hasDerivAt_id (1 : ℂ)
  have h := (hasDerivAt_const (1 : ℂ) (1 : ℂ)).sub hid
  simpa only [Pi.sub_apply, zero_sub] using h

lemma hasDerivAt_motzkinSecondNoS_one :
    HasDerivAt motzkinSecondNoS 0 (1 : ℂ) := by
  have h1 := HasDerivAt.const_mul (3 * motzkinSqrtThreeℂ) hasDerivAt_one_sub_div_three
  have h2 := HasDerivAt.const_mul (3 : ℂ) hasDerivAt_motzkinSqrtPlus_one
  have h3 :=
    (HasDerivAt.const_mul motzkinAnalyticLinearCoeff
      hasDerivAt_motzkinSqrtPlus_one).mul hasDerivAt_one_sub
  have h4 :=
    (HasDerivAt.const_mul motzkinSecondSingularCoeff hasDerivAt_one_sub).mul
      hasDerivAt_one_sub_div_three
  have hcalc := (h1.sub h2).sub h3 |>.sub h4
  convert hcalc using 1
  rw [motzkinSqrtPlus_one]
  unfold motzkinAnalyticLinearCoeff motzkinSecondSingularCoeff motzkinSqrtThreeℂ
  have hs3 : ((Real.sqrt 3 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 3))
  norm_num [Complex.ofReal_div, Complex.ofReal_mul]
  field_simp [hs3]
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

lemma hasDerivAt_motzkinSecondSqrtCoeff_one :
    HasDerivAt motzkinSecondSqrtCoeff (-8 : ℂ) (1 : ℂ) := by
  have h0 := HasDerivAt.const_add (-1 : ℂ)
    (HasDerivAt.const_mul (3 * motzkinSqrtThreeℂ) hasDerivAt_motzkinSqrtPlus_one)
  have h2 := HasDerivAt.const_mul motzkinAnalyticLinearCoeff
    hasDerivAt_one_sub_div_three
  have h3 :=
    (HasDerivAt.const_mul motzkinSecondSingularCoeff
      hasDerivAt_motzkinSqrtPlus_one).mul hasDerivAt_one_sub
  have hcalc := (h0.sub h2).sub h3
  convert hcalc using 1
  rw [motzkinSqrtPlus_one]
  unfold motzkinAnalyticLinearCoeff motzkinSecondSingularCoeff motzkinSqrtThreeℂ
  have hs3 : ((Real.sqrt 3 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 3))
  norm_num [Complex.ofReal_div, Complex.ofReal_mul]
  field_simp [hs3]
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

private lemma nhdsWithin_motzkin_delta_le_punctured :
    𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ) ≤
      𝓝[({1}ᶜ : Set ℂ)] (1 : ℂ) := by
  exact nhdsWithin_mono _ (by intro z hz; exact hz.2.1)

lemma tendsto_motzkinSecondNoS_div :
    Tendsto (fun z : ℂ => motzkinSecondNoS z / (1 - z))
      (𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)) (𝓝 0) := by
  let l := 𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)
  have hslope : Tendsto (slope motzkinSecondNoS (1 : ℂ)) l (𝓝 (0 : ℂ)) :=
    hasDerivAt_motzkinSecondNoS_one.tendsto_slope.mono_left
      nhdsWithin_motzkin_delta_le_punctured
  have hneg : Tendsto (fun z : ℂ => -slope motzkinSecondNoS (1 : ℂ) z) l
      (𝓝 (0 : ℂ)) := by
    simpa using hslope.neg
  refine hneg.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz_ne : z ≠ 1 := hz.2.1
  have h1z : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz_ne)
  have hz1 : z - (1 : ℂ) ≠ 0 := sub_ne_zero.mpr hz_ne
  simp [slope, motzkinSecondNoS_one, div_eq_mul_inv]
  field_simp [h1z, hz1]
  ring

lemma tendsto_motzkinSecondSqrtCoeff_div :
    Tendsto (fun z : ℂ => motzkinSecondSqrtCoeff z / (1 - z))
      (𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)) (𝓝 (8 : ℂ)) := by
  let l := 𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)
  have hslope : Tendsto (slope motzkinSecondSqrtCoeff (1 : ℂ)) l (𝓝 (-8 : ℂ)) :=
    hasDerivAt_motzkinSecondSqrtCoeff_one.tendsto_slope.mono_left
      nhdsWithin_motzkin_delta_le_punctured
  have hneg : Tendsto (fun z : ℂ => -slope motzkinSecondSqrtCoeff (1 : ℂ) z) l
      (𝓝 (8 : ℂ)) := by
    simpa using hslope.neg
  refine hneg.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz_ne : z ≠ 1 := hz.2.1
  have h1z : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz_ne)
  have hz1 : z - (1 : ℂ) ≠ 0 := sub_ne_zero.mpr hz_ne
  simp [slope, motzkinSecondSqrtCoeff_one, div_eq_mul_inv]
  field_simp [h1z, hz1]
  ring

lemma motzkinSecondQuotient_decomp (z : ℂ) :
    motzkinSingularityQuotientModel z -
        motzkinAnalyticLinearCoeff * motzkinSqrtOneSub z -
        motzkinSecondSingularCoeff * (1 - z) =
      (motzkinSecondNoS z + motzkinSqrtOneSub z * motzkinSecondSqrtCoeff z) /
        motzkinRescaledDenominator z := by
  set s := motzkinSqrtOneSub z with hs_def
  set t := motzkinSqrtPlus z with ht_def
  have hs_sq : s ^ 2 = 1 - z := by
    rw [hs_def]
    exact motzkinSqrtOneSub_sq z
  have hz_eq : z = 1 - s ^ 2 := by
    rw [hs_sq]
    ring
  have hd : 1 - z / 3 + t * s ≠ 0 := by
    rw [hs_def, ht_def]
    exact motzkinRescaledDenominator_ne_zero z
  unfold motzkinSingularityQuotientModel motzkinSecondNoS motzkinSecondSqrtCoeff
    motzkinRescaledDenominator motzkinSqrtThreeℂ motzkinAnalyticLinearCoeff
    motzkinSecondSingularCoeff
  rw [← hs_def, ← ht_def]
  rw [eq_div_iff hd]
  rw [sub_mul, sub_mul]
  rw [div_mul_cancel₀ _ hd]
  rw [hz_eq]
  ring

lemma motzkinSecondQuotient_div_eq {z : ℂ} (hz : z ≠ 1) :
    (motzkinSingularityQuotientModel z -
        motzkinAnalyticLinearCoeff * motzkinSqrtOneSub z -
        motzkinSecondSingularCoeff * (1 - z)) / (1 - z) =
      (motzkinSecondNoS z / (1 - z) +
          motzkinSqrtOneSub z * (motzkinSecondSqrtCoeff z / (1 - z))) /
        motzkinRescaledDenominator z := by
  rw [motzkinSecondQuotient_decomp z]
  have h1z : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  have hd := motzkinRescaledDenominator_ne_zero z
  field_simp [h1z, hd]

lemma tendsto_motzkinSecondQuotient_div :
    Tendsto
      (fun z : ℂ =>
        (motzkinSingularityQuotientModel z -
          motzkinAnalyticLinearCoeff * motzkinSqrtOneSub z -
          motzkinSecondSingularCoeff * (1 - z)) / (1 - z))
      (𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)) (𝓝 0) := by
  let l := 𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)
  have hnum : Tendsto
      (fun z : ℂ =>
        motzkinSecondNoS z / (1 - z) +
          motzkinSqrtOneSub z * (motzkinSecondSqrtCoeff z / (1 - z))) l
      (𝓝 (0 + 0 * (8 : ℂ))) := by
    exact tendsto_motzkinSecondNoS_div.add
      (tendsto_motzkinSqrtOneSub.mul tendsto_motzkinSecondSqrtCoeff_div)
  have hquot := hnum.div tendsto_motzkinRescaledDenominator
    (by norm_num : (2 / 3 : ℂ) ≠ 0)
  have hquot0 : Tendsto
      (fun z : ℂ =>
        (motzkinSecondNoS z / (1 - z) +
            motzkinSqrtOneSub z * (motzkinSecondSqrtCoeff z / (1 - z))) /
          motzkinRescaledDenominator z) l (𝓝 0) := by
    convert hquot using 1
    norm_num
  refine hquot0.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (motzkinSecondQuotient_div_eq hz.2.1).symm

lemma tendsto_motzkinSecondQuotient_twoTerm :
    Tendsto
      (fun z : ℂ =>
        ‖motzkinSingularityQuotientModel z -
            motzkinAnalyticLinearCoeff * motzkinSqrtOneSub z -
            motzkinSecondSingularCoeff * (1 - z)‖ *
          ‖(1 : ℂ) - z‖ ^ (-(1 : ℝ)))
      (𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)) (𝓝 0) := by
  let l := 𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)
  have hnorm : Tendsto
      (fun z : ℂ =>
        ‖(motzkinSingularityQuotientModel z -
          motzkinAnalyticLinearCoeff * motzkinSqrtOneSub z -
          motzkinSecondSingularCoeff * (1 - z)) / (1 - z)‖) l (𝓝 0) := by
    simpa using tendsto_motzkinSecondQuotient_div.norm
  refine hnorm.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz_ne : z ≠ 1 := hz.2.1
  have h1z : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz_ne)
  rw [Real.rpow_neg (norm_nonneg ((1 : ℂ) - z)), Real.rpow_one]
  rw [show
      ‖motzkinSingularityQuotientModel z -
          motzkinAnalyticLinearCoeff * motzkinSqrtOneSub z -
          motzkinSecondSingularCoeff * (1 - z)‖ * ‖(1 : ℂ) - z‖⁻¹ =
        ‖motzkinSingularityQuotientModel z -
          motzkinAnalyticLinearCoeff * motzkinSqrtOneSub z -
          motzkinSecondSingularCoeff * (1 - z)‖ / ‖(1 : ℂ) - z‖ by
        rw [div_eq_mul_inv]]
  rw [← norm_div]

lemma motzkin_adjusted_residual_eq {z : ℂ} (hz : z ≠ 1) :
    motzkinAdjustedRescaledFun z -
        motzkinSingularCoeff * (1 - z) ^ (1 / 2 : ℂ) -
        motzkinSecondSingularCoeff * (1 - z) ^ (3 / 2 : ℂ) =
      motzkinSqrtOneSub z *
        (motzkinSingularityQuotientModel z -
          motzkinAnalyticLinearCoeff * motzkinSqrtOneSub z -
          motzkinSecondSingularCoeff * (1 - z)) := by
  let s := motzkinSqrtOneSub z
  have hs_ne : s ≠ 0 := by
    dsimp [s]
    exact motzkinSqrtOneSub_ne_zero_of_ne_one hz
  have hQ := motzkin_singularity_quotient_eq hz
  have hcenter : motzkinCenteredRescaledFun z - motzkinSingularCoeff * s =
      motzkinSingularityQuotientModel z * s := by
    have hmul := congrArg (fun w : ℂ => w * s) hQ
    dsimp [s] at hmul ⊢
    rw [div_mul_cancel₀ _ hs_ne] at hmul
    exact hmul
  have hs_sq : s ^ 2 = 1 - z := by
    dsimp [s]
    exact motzkinSqrtOneSub_sq z
  have hu_ne : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  have hpow_three_halves : (1 - z) ^ (3 / 2 : ℂ) = (1 - z) * s := by
    dsimp [s]
    rw [show (3 / 2 : ℂ) = 1 + (1 / 2 : ℂ) by norm_num]
    rw [Complex.cpow_add _ _ hu_ne, Complex.cpow_one]
    rfl
  unfold motzkinAdjustedRescaledFun
  change motzkinCenteredRescaledFun z - motzkinAnalyticLinearCoeff * (1 - z) -
      motzkinSingularCoeff * motzkinSqrtOneSub z -
      motzkinSecondSingularCoeff * (1 - z) ^ (3 / 2 : ℂ) =
    motzkinSqrtOneSub z *
      (motzkinSingularityQuotientModel z -
        motzkinAnalyticLinearCoeff * motzkinSqrtOneSub z -
        motzkinSecondSingularCoeff * (1 - z))
  rw [hpow_three_halves]
  rw [show motzkinCenteredRescaledFun z - motzkinAnalyticLinearCoeff * (1 - z) -
      motzkinSingularCoeff * motzkinSqrtOneSub z -
      motzkinSecondSingularCoeff * ((1 - z) * motzkinSqrtOneSub z) =
      (motzkinCenteredRescaledFun z - motzkinSingularCoeff * motzkinSqrtOneSub z) -
        motzkinAnalyticLinearCoeff * (1 - z) -
        motzkinSecondSingularCoeff * ((1 - z) * motzkinSqrtOneSub z) by ring]
  dsimp [s] at hcenter hs_sq
  rw [hcenter]
  rw [← hs_sq]
  ring

lemma motzkin_adjusted_singularity_twoTerm_norm_eq {z : ℂ} (hz : z ≠ 1) :
    ‖motzkinAdjustedRescaledFun z -
        motzkinSingularCoeff * (1 - z) ^ (1 / 2 : ℂ) -
        motzkinSecondSingularCoeff * (1 - z) ^ (3 / 2 : ℂ)‖ *
      ‖(1 : ℂ) - z‖ ^ (-(3 / 2 : ℝ)) =
    ‖motzkinSingularityQuotientModel z -
        motzkinAnalyticLinearCoeff * motzkinSqrtOneSub z -
        motzkinSecondSingularCoeff * (1 - z)‖ *
      ‖(1 : ℂ) - z‖ ^ (-(1 : ℝ)) := by
  let u : ℂ := 1 - z
  have hu_ne : u ≠ 0 := by
    dsimp [u]
    exact sub_ne_zero.mpr (Ne.symm hz)
  have hu_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu_ne
  have hs_norm : ‖motzkinSqrtOneSub z‖ = ‖u‖ ^ (1 / 2 : ℝ) := by
    dsimp [u]
    unfold motzkinSqrtOneSub
    convert Complex.norm_cpow_real ((1 : ℂ) - z) (1 / 2 : ℝ) using 1
    norm_num
  rw [motzkin_adjusted_residual_eq hz]
  rw [norm_mul, hs_norm]
  change (‖u‖ ^ (1 / 2 : ℝ) *
        ‖motzkinSingularityQuotientModel z -
          motzkinAnalyticLinearCoeff * motzkinSqrtOneSub z -
          motzkinSecondSingularCoeff * (1 - z)‖) *
      ‖u‖ ^ (-(3 / 2 : ℝ)) =
    ‖motzkinSingularityQuotientModel z -
        motzkinAnalyticLinearCoeff * motzkinSqrtOneSub z -
        motzkinSecondSingularCoeff * (1 - z)‖ *
      ‖u‖ ^ (-(1 : ℝ))
  have hpow : ‖u‖ ^ (1 / 2 : ℝ) * ‖u‖ ^ (-(3 / 2 : ℝ)) =
      ‖u‖ ^ (-(1 : ℝ)) := by
    rw [← Real.rpow_add hu_pos]
    norm_num
  rw [show ‖u‖ ^ (1 / 2 : ℝ) *
        ‖motzkinSingularityQuotientModel z -
          motzkinAnalyticLinearCoeff * motzkinSqrtOneSub z -
          motzkinSecondSingularCoeff * (1 - z)‖ * ‖u‖ ^ (-(3 / 2 : ℝ)) =
      ‖motzkinSingularityQuotientModel z -
          motzkinAnalyticLinearCoeff * motzkinSqrtOneSub z -
          motzkinSecondSingularCoeff * (1 - z)‖ *
        (‖u‖ ^ (1 / 2 : ℝ) * ‖u‖ ^ (-(3 / 2 : ℝ))) by ring, hpow]

lemma motzkinAdjustedRescaledFun_singularity_twoTerm :
    Tendsto
      (fun z : ℂ =>
        ‖motzkinAdjustedRescaledFun z -
            motzkinSingularCoeff * (1 - z) ^ (1 / 2 : ℂ) -
            motzkinSecondSingularCoeff * (1 - z) ^ (3 / 2 : ℂ)‖ *
          ‖(1 : ℂ) - z‖ ^ (-(3 / 2 : ℝ)))
      (𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)) (𝓝 0) := by
  refine tendsto_motzkinSecondQuotient_twoTerm.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (motzkin_adjusted_singularity_twoTerm_norm_eq hz.2.1).symm

lemma motzkin_neg_half_pole :
    ∀ m : ℕ, (-(1 / 2 : ℝ)) ≠ 1 - (m : ℝ) := by
  intro m h
  have hm2R : (2 * m : ℝ) = 3 := by nlinarith
  have hm2N : 2 * m = 3 := by exact_mod_cast hm2R
  omega

lemma motzkin_Real_Gamma_neg_half :
    Real.Gamma (-(1 / 2 : ℝ)) = -2 * Real.sqrt Real.pi := by
  have h := Real.Gamma_add_one (s := (-(1 / 2 : ℝ)))
    (by norm_num : (-(1 / 2 : ℝ)) ≠ 0)
  norm_num at h
  rw [Real.Gamma_one_half_eq] at h
  linarith

lemma motzkin_Real_Gamma_neg_three_halves :
    Real.Gamma (-(3 / 2 : ℝ)) = 4 * Real.sqrt Real.pi / 3 := by
  have h := Real.Gamma_add_one (s := (-(3 / 2 : ℝ)))
    (by norm_num : (-(3 / 2 : ℝ)) ≠ 0)
  norm_num at h
  rw [motzkin_Real_Gamma_neg_half] at h
  nlinarith

lemma motzkin_secondOrder_model_complex_eq (n : ℕ) :
    (motzkinSingularCoeff *
        ((((n : ℝ) ^ ((-(1 / 2 : ℝ)) - 1) /
              Real.Gamma (-(1 / 2 : ℝ)) : ℝ) : ℂ) +
          ((((-(1 / 2 : ℝ)) * ((-(1 / 2 : ℝ)) - 1) / 2 /
                Real.Gamma (-(1 / 2 : ℝ))) *
              (n : ℝ) ^ ((-(1 / 2 : ℝ)) - 2) : ℝ) : ℂ)) +
      motzkinSecondSingularCoeff *
        (((n : ℝ) ^ ((-(1 / 2 : ℝ)) - 2) /
          Real.Gamma ((-(1 / 2 : ℝ)) - 1) : ℝ) : ℂ)) =
      (((motzkinAsymptoticConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
          motzkinSecondAsymptoticConstant * (n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ)) := by
  have hpow1 : (n : ℝ) ^ ((-(1 / 2 : ℝ)) - 1) =
      (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
    congr 1
    norm_num
  have hpow2 : (n : ℝ) ^ ((-(1 / 2 : ℝ)) - 2) =
      (n : ℝ) ^ (-(5 / 2 : ℝ)) := by
    congr 1
    norm_num
  rw [hpow1, hpow2]
  unfold motzkinSingularCoeff motzkinSecondSingularCoeff
    motzkinAsymptoticConstant motzkinSecondAsymptoticConstant
  rw [motzkin_Real_Gamma_neg_half,
    show (-(1 / 2 : ℝ)) - 1 = -(3 / 2 : ℝ) by norm_num,
    motzkin_Real_Gamma_neg_three_halves]
  norm_num [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_neg]
  ring

theorem motzkinAdjustedRescaledCoeff_secondOrder_of_singularity
    (hsing : Tendsto
      (fun z : ℂ =>
        ‖motzkinAdjustedRescaledFun z -
            motzkinSingularCoeff * (1 - z) ^ (1 / 2 : ℂ) -
            motzkinSecondSingularCoeff * (1 - z) ^ (3 / 2 : ℂ)‖ *
          ‖(1 : ℂ) - z‖ ^ (-(3 / 2 : ℝ)))
      (𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)) (𝓝 0)) :
    (fun n : ℕ =>
      motzkinAdjustedRescaledFMLS.coeff n -
        (((motzkinAsymptoticConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
            motzkinSecondAsymptoticConstant * (n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ)))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(5 / 2 : ℝ))) := by
  have htransfer := transfer_twoTerm_secondOrder_general
    (α := (-(1 / 2 : ℝ))) (C0 := motzkinSingularCoeff)
    (C1 := motzkinSecondSingularCoeff)
    (R := (3 / 2 : ℝ)) (φ := Real.pi / 4)
    (f := motzkinAdjustedRescaledFun) (p := motzkinAdjustedRescaledFMLS)
    motzkin_neg_half_pole (by norm_num) (by positivity) ?_
    motzkinAdjustedRescaledFun_hasFPowerSeriesAt_zero
    analyticOnNhd_motzkinAdjustedRescaledFun ?_
  · have hcomplex :
        (fun n : ℕ =>
          motzkinAdjustedRescaledFMLS.coeff n -
            (((motzkinAsymptoticConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
                motzkinSecondAsymptoticConstant * (n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ)))
          =o[atTop] (fun n : ℕ => (n : ℝ) ^ ((-(1 / 2 : ℝ)) - 2)) := by
      refine htransfer.congr_left ?_
      intro n
      rw [motzkin_secondOrder_model_complex_eq n]
    convert hcomplex using 1
    ext n
    congr 1
    norm_num
  · nlinarith [Real.pi_pos]
  · convert hsing using 1
    ext z
    norm_num

theorem motzkinCenteredRescaledCoeff_secondOrder_of_singularity
    (hsing : Tendsto
      (fun z : ℂ =>
        ‖motzkinAdjustedRescaledFun z -
            motzkinSingularCoeff * (1 - z) ^ (1 / 2 : ℂ) -
            motzkinSecondSingularCoeff * (1 - z) ^ (3 / 2 : ℂ)‖ *
          ‖(1 : ℂ) - z‖ ^ (-(3 / 2 : ℝ)))
      (𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)) (𝓝 0)) :
    (fun n : ℕ =>
      (PowerSeries.toFMLS motzkinCenteredRescaledSeriesℂ).coeff n -
        (((motzkinAsymptoticConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
            motzkinSecondAsymptoticConstant * (n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ)))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(5 / 2 : ℝ))) := by
  have h := motzkinAdjustedRescaledCoeff_secondOrder_of_singularity hsing
  refine h.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_ge_atTop 2] with n hn
  rw [coeff_motzkinAdjustedRescaledFMLS_of_two_le hn]

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

theorem motzkinRescaled_complex_secondOrder_of_singularity
    (hsing : Tendsto
      (fun z : ℂ =>
        ‖motzkinAdjustedRescaledFun z -
            motzkinSingularCoeff * (1 - z) ^ (1 / 2 : ℂ) -
            motzkinSecondSingularCoeff * (1 - z) ^ (3 / 2 : ℂ)‖ *
          ‖(1 : ℂ) - z‖ ^ (-(3 / 2 : ℝ)))
      (𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)) (𝓝 0)) :
    (fun n : ℕ =>
      (motzkin n : ℂ) * ((3 : ℂ)⁻¹) ^ n -
        (((motzkinAsymptoticConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
            motzkinSecondAsymptoticConstant * (n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ)))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(5 / 2 : ℝ))) := by
  have hcenter := motzkinCenteredRescaledCoeff_secondOrder_of_singularity hsing
  refine hcenter.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_ne_atTop 0] with n hn
  rw [PowerSeries.coeff_toFMLS, coeff_motzkinCenteredRescaledSeriesℂ_of_ne_zero hn,
    coeff_motzkinRescaledSeriesℂ]

lemma motzkinSecondAsymptoticConstant_eq_relative :
    motzkinSecondAsymptoticConstant =
      motzkinAsymptoticConstant * motzkinRelativeSecondConstant := by
  unfold motzkinSecondAsymptoticConstant motzkinAsymptoticConstant
    motzkinRelativeSecondConstant
  ring

theorem motzkinAdjustedRescaledCoeff_secondOrder :
    (fun n : ℕ =>
      motzkinAdjustedRescaledFMLS.coeff n -
        (((motzkinAsymptoticConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
            motzkinSecondAsymptoticConstant * (n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ)))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(5 / 2 : ℝ))) :=
  motzkinAdjustedRescaledCoeff_secondOrder_of_singularity
    motzkinAdjustedRescaledFun_singularity_twoTerm

theorem motzkinCenteredRescaledCoeff_secondOrder :
    (fun n : ℕ =>
      (PowerSeries.toFMLS motzkinCenteredRescaledSeriesℂ).coeff n -
        (((motzkinAsymptoticConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
            motzkinSecondAsymptoticConstant * (n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ)))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(5 / 2 : ℝ))) :=
  motzkinCenteredRescaledCoeff_secondOrder_of_singularity
    motzkinAdjustedRescaledFun_singularity_twoTerm

theorem motzkinRescaled_complex_secondOrder :
    (fun n : ℕ =>
      (motzkin n : ℂ) * ((3 : ℂ)⁻¹) ^ n -
        (((motzkinAsymptoticConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
            motzkinSecondAsymptoticConstant * (n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ)))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(5 / 2 : ℝ))) :=
  motzkinRescaled_complex_secondOrder_of_singularity
    motzkinAdjustedRescaledFun_singularity_twoTerm

theorem motzkinRescaled_secondOrder :
    (fun n : ℕ =>
      (motzkin n : ℝ) * ((3 : ℝ)⁻¹) ^ n -
        (motzkinAsymptoticConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
          motzkinSecondAsymptoticConstant * (n : ℝ) ^ (-(5 / 2 : ℝ))))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(5 / 2 : ℝ))) := by
  have hcomplex :
      (fun n : ℕ =>
        (((motzkin n : ℝ) * ((3 : ℝ)⁻¹) ^ n : ℝ) : ℂ) -
          (((motzkinAsymptoticConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
              motzkinSecondAsymptoticConstant * (n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ)))
        =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(5 / 2 : ℝ))) := by
    refine motzkinRescaled_complex_secondOrder.congr_left ?_
    intro n
    have hpow : ((3 : ℂ)⁻¹) ^ n = ((((3 : ℝ)⁻¹) ^ n : ℝ) : ℂ) := by
      have hbase : (3 : ℂ)⁻¹ = (((3 : ℝ)⁻¹ : ℝ) : ℂ) := by
        rw [Complex.ofReal_inv]
        norm_num
      rw [hbase, Complex.ofReal_pow]
    have hcoeff :
        (motzkin n : ℂ) * ((3 : ℂ)⁻¹) ^ n =
          (((motzkin n : ℝ) * ((3 : ℝ)⁻¹) ^ n : ℝ) : ℂ) := by
      rw [hpow]
      norm_num [Complex.ofReal_mul]
    rw [hcoeff]
  have hreal := complex_re_isLittleO_ofReal hcomplex
  refine hreal.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards with n
  rw [Complex.ofReal_re]

theorem motzkin_secondOrder_additive :
    (fun n : ℕ =>
      (motzkin n : ℝ) -
        (3 : ℝ) ^ n *
          (motzkinAsymptoticConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
            motzkinSecondAsymptoticConstant * (n : ℝ) ^ (-(5 / 2 : ℝ))))
      =o[atTop]
        (fun n : ℕ => (3 : ℝ) ^ n * (n : ℝ) ^ (-(5 / 2 : ℝ))) := by
  have hmul := motzkinRescaled_secondOrder.mul_isBigO
    (isBigO_refl (fun n : ℕ => (3 : ℝ) ^ n) atTop)
  refine hmul.congr' ?_ ?_
  · filter_upwards with n
    have h3 : (3 : ℝ) ≠ 0 := by norm_num
    calc
      ((motzkin n : ℝ) * ((3 : ℝ)⁻¹) ^ n -
          (motzkinAsymptoticConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
            motzkinSecondAsymptoticConstant * (n : ℝ) ^ (-(5 / 2 : ℝ)))) *
          (3 : ℝ) ^ n
          = (motzkin n : ℝ) * (((3 : ℝ)⁻¹) ^ n * (3 : ℝ) ^ n) -
              (3 : ℝ) ^ n *
                (motzkinAsymptoticConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
                  motzkinSecondAsymptoticConstant * (n : ℝ) ^ (-(5 / 2 : ℝ))) := by
            ring
      _ = (motzkin n : ℝ) -
              (3 : ℝ) ^ n *
                (motzkinAsymptoticConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
                  motzkinSecondAsymptoticConstant * (n : ℝ) ^ (-(5 / 2 : ℝ))) := by
            rw [← mul_pow, inv_mul_cancel₀ h3, one_pow, mul_one]
  · filter_upwards with n
    ring

theorem motzkin_secondOrder :
    (fun n : ℕ =>
      (motzkin n : ℝ) -
        (3 : ℝ) ^ n * motzkinAsymptoticConstant *
          (n : ℝ) ^ (-(3 / 2 : ℝ)) *
          (1 + motzkinRelativeSecondConstant * (n : ℝ) ^ (-(1 : ℝ))))
      =o[atTop]
        (fun n : ℕ => (3 : ℝ) ^ n * (n : ℝ) ^ (-(5 / 2 : ℝ))) := by
  refine motzkin_secondOrder_additive.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ)) hn)
  have hpow : (n : ℝ) ^ (-(5 / 2 : ℝ)) =
      (n : ℝ) ^ (-(3 / 2 : ℝ)) * (n : ℝ) ^ (-(1 : ℝ)) := by
    rw [← Real.rpow_add hnpos]
    norm_num
  rw [motzkinSecondAsymptoticConstant_eq_relative, hpow]
  ring

end
