import AnalyticCombinatorics.Ch7.SingularityApp.CycleMarkedPermPairBoth
import AnalyticCombinatorics.Ch7.SingularityApp.UndirectedCycleMarkedPermPairs
import AnalyticCombinatorics.Ch4.Analytic.LogSqTransferNatural

/-!
# A class that GENUINELY needs the natural-remainder log² transfer (~½·n·(log n)²)

`undirectedCycleLogSqPermPairClass := undirectedCycleClass ⋆ cycleMarkedPermPairClass` — an
undirected cycle (length ≥ 3) together with an ordered pair of permutations one of whose cycles is
distinguished — has EGF

  `(½·log(1/(1-z)) - z/2 - z²/4) · log(1/(1-z)) · (1-z)^{-2}`
    `= ½·(1-z)^{-2}·(-log(1-z))²  -  (z/2 + z²/4)·(1-z)^{-2}·(-log(1-z))`.

The residual `R(z) = -(z/2+z²/4)·(1-z)^{-2}·(-log(1-z))` has `‖R‖·‖1-z‖² ≍ |log(1-z)| → ∞`
(so it is NOT `o(|1-z|^{-2})` — the *strong* log² transfer fails), yet
`‖R‖·‖1-z‖²/log²(1/|1-z|) → 0` (so the *natural* log² transfer applies).  Hence

  `aₙ / n! ~ ½·n·(log n)²`.

This is the first class requiring the natural-remainder log² transfer (analog of
`undirectedCycleMarkedPermPairs` for log¹).  (Construction from ChatGPT-Pro ac/ac2.)
-/

open Complex Filter Asymptotics
open scoped BigOperators PowerSeries Topology

noncomputable section

namespace AnalyticCombinatorics

open AnalyticCombinatorics.Ch1
open AnalyticCombinatorics.Ch5.Meromorphic.Alignments

/-- Undirected cycle ⋆ (pair of permutations with a marked cycle). -/
def undirectedCycleLogSqPermPairClass : CombClass :=
  TwoRegularClass.undirectedCycleClass.lprod cycleMarkedPermPairClass

theorem mapℂ_undirectedCycleLogSqPermPairClass_egf :
    PowerSeries.mapℂ undirectedCycleLogSqPermPairClass.egf
      = TwoRegularClass.twoRegularCoreEGFℂ * logSingularityGF 2 := by
  rw [undirectedCycleLogSqPermPairClass, CombClass.egf_lprod, map_mul,
    mapℂ_cycleMarkedPermPairClass_egf, TwoRegularClass.twoRegularCoreEGFℂ]

/-- Analytic carrier `twoRegularCoreFun(z)·logSingularityFun 2 z`. -/
def undirectedCycleLogSqPermPairFun (z : ℂ) : ℂ :=
  TwoRegularClass.twoRegularCoreFun z * logSingularityFun ((2 : ℝ) : ℂ) z

/-- `twoRegularCoreFun` is `Δ`-analytic. -/
lemma analyticOnNhd_twoRegularCoreFun_deltaDomain {R φ : ℝ} (hφ0 : 0 < φ) :
    AnalyticOnNhd ℂ TwoRegularClass.twoRegularCoreFun (DeltaDomainArg R φ) := by
  have hneglog : AnalyticOnNhd ℂ (fun z : ℂ => -Complex.log (1 - z)) (DeltaDomainArg R φ) :=
    analyticOnNhd_negLog_one_sub_deltaDomain hφ0
  have hfeq : TwoRegularClass.twoRegularCoreFun
      = fun z : ℂ => (2⁻¹ : ℂ) * (-Complex.log (1 - z)) - (2⁻¹ : ℂ) * z - (4⁻¹ : ℂ) * z ^ 2 := by
    funext z
    simp only [TwoRegularClass.twoRegularCoreFun, cycleAnalyticFun, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
  rw [hfeq]
  exact ((analyticOnNhd_const.mul hneglog).sub (analyticOnNhd_const.mul analyticOnNhd_id)).sub
    (analyticOnNhd_const.mul (analyticOnNhd_id.pow 2))

lemma analyticOnNhd_undirectedCycleLogSqPermPairFun_deltaDomain {R φ : ℝ}
    (hφ0 : 0 < φ) (hφπ : φ < Real.pi) :
    AnalyticOnNhd ℂ undirectedCycleLogSqPermPairFun (DeltaDomainArg R φ) :=
  (analyticOnNhd_twoRegularCoreFun_deltaDomain hφ0).mul
    (analyticOnNhd_logSingularityFun_deltaDomain hφ0 hφπ)

/-- Faithfulness: power series of the carrier is `mapℂ A.egf` (double Cauchy product). -/
lemma undirectedCycleLogSqPermPairFun_hasFPowerSeriesAt :
    HasFPowerSeriesAt undirectedCycleLogSqPermPairFun
      (PowerSeries.toFMLS (PowerSeries.mapℂ undirectedCycleLogSqPermPairClass.egf)) 0 := by
  rw [hasFPowerSeriesAt_iff]
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with z hz
  have hz_norm : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hz
  have hlogModel := hasSum_powerSeries_mul (oneSubCpowGF (2 : ℂ)) logGF
    (oneSubCpowGF_hasSum (α := (2 : ℂ)) hz_norm) (logGF_hasSum hz_norm)
    (oneSubCpowGF_summable_norm (α := (2 : ℂ)) hz_norm) (logGF_summable_norm hz_norm)
  rw [← logSingularityGF] at hlogModel
  have hprod := hasSum_powerSeries_mul TwoRegularClass.twoRegularCoreEGFℂ (logSingularityGF (2 : ℂ))
    (twoRegularCore_hasSum hz_norm) hlogModel
    (twoRegularCore_summable_norm hz_norm) (logSingularityGF_summable_norm (α := (2 : ℂ)) hz_norm)
  rw [← mapℂ_undirectedCycleLogSqPermPairClass_egf] at hprod
  have hval : TwoRegularClass.twoRegularCoreFun z * ((1 - z) ^ (-(2 : ℂ)) * -Complex.log (1 - z))
      = undirectedCycleLogSqPermPairFun z := by
    rw [undirectedCycleLogSqPermPairFun, logSingularityFun,
      show ((2 : ℝ) : ℂ) = (2 : ℂ) by norm_num]
  rw [hval] at hprod
  simpa [PowerSeries.coeff_toFMLS, smul_eq_mul, mul_comm] using hprod

/-- The residual identity `f - ½·logSqModel = -(½z+¼z²)·logSingularityFun 2`. -/
lemma undirectedCycleLogSqPermPairFun_residual (z : ℂ) :
    undirectedCycleLogSqPermPairFun z - (1 / 2 : ℂ) * logSqSingularityFun ((2 : ℝ) : ℂ) z
      = -((1 / 2 : ℂ) * z + (1 / 4 : ℂ) * z ^ 2) * logSingularityFun ((2 : ℝ) : ℂ) z := by
  simp only [undirectedCycleLogSqPermPairFun, TwoRegularClass.twoRegularCoreFun, cycleAnalyticFun,
    logSqSingularityFun, logSingularityFun, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [show ((2 : ℝ) : ℂ) = (2 : ℂ) by norm_num]
  ring

/-- `‖-log(1-z)‖ / log²(1/‖1-z‖) → 0` near `1`. -/
lemma negLog_over_logSq_tendsto_zero {R φ : ℝ} :
    Tendsto (fun z : ℂ => ‖-Complex.log (1 - z)‖ * ((Real.log (‖(1 : ℂ) - z‖⁻¹)) ^ 2)⁻¹)
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0) := by
  have hnorm0 : Tendsto (fun z : ℂ => ‖(1 : ℂ) - z‖) (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    have h : Continuous (fun z : ℂ => ‖(1 : ℂ) - z‖) := by fun_prop
    simpa using h.tendsto 1
  have hLatTop : Tendsto (fun z : ℂ => Real.log (‖(1 : ℂ) - z‖⁻¹))
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) atTop := by
    have hinv : Tendsto (fun z : ℂ => ‖(1 : ℂ) - z‖⁻¹) (𝓝[DeltaDomainArg R φ] (1 : ℂ)) atTop := by
      apply Filter.Tendsto.comp tendsto_inv_nhdsGT_zero
      rw [tendsto_nhdsWithin_iff]
      refine ⟨hnorm0, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hz.2.1))
    exact Real.tendsto_log_atTop.comp hinv
  -- upper bound (L+π)/L² → 0
  have hub : Tendsto (fun z : ℂ => (Real.log (‖(1 : ℂ) - z‖⁻¹) + Real.pi)
      * ((Real.log (‖(1 : ℂ) - z‖⁻¹)) ^ 2)⁻¹) (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0) := by
    have hcomp : Tendsto (fun L : ℝ => (L + Real.pi) * (L ^ 2)⁻¹) atTop (𝓝 0) := by
      have : (fun L : ℝ => (L + Real.pi) * (L ^ 2)⁻¹) =ᶠ[atTop]
          (fun L : ℝ => L⁻¹ + Real.pi * (L ^ 2)⁻¹) := by
        filter_upwards [eventually_gt_atTop 0] with L hL
        field_simp
      rw [tendsto_congr' this]
      have h1 : Tendsto (fun L : ℝ => L⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
      have h2 : Tendsto (fun L : ℝ => Real.pi * (L ^ 2)⁻¹) atTop (𝓝 0) := by
        have := (tendsto_inv_atTop_zero.comp
          (tendsto_pow_atTop (by norm_num : 2 ≠ 0))).const_mul Real.pi
        simpa using this
      simpa using h1.add h2
    exact hcomp.comp hLatTop
  refine squeeze_zero' (Eventually.of_forall fun z => by positivity) ?_ hub
  filter_upwards [hnorm0.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    self_mem_nhdsWithin] with z hz1 hzΔ
  have hz_ne : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hzΔ.2.1)
  have hnpos : 0 < ‖(1 : ℂ) - z‖ := norm_pos_iff.mpr hz_ne
  have hn1 : ‖(1 : ℂ) - z‖ < 1 := by simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using hz1
  have hLpos : 0 < Real.log (‖(1 : ℂ) - z‖⁻¹) := by
    rw [Real.log_inv]; have := Real.log_neg hnpos hn1; linarith
  have hlogbound : ‖-Complex.log (1 - z)‖ ≤ Real.log (‖(1 : ℂ) - z‖⁻¹) + Real.pi := by
    rw [norm_neg]
    have h1 : ‖Complex.log (1 - z)‖
        ≤ |(Complex.log (1 - z)).re| + |(Complex.log (1 - z)).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    rw [Complex.log_re, Complex.log_im] at h1
    have harg : |Complex.arg (1 - z)| ≤ Real.pi := Complex.abs_arg_le_pi _
    have hlog : |Real.log ‖(1 : ℂ) - z‖| = Real.log (‖(1 : ℂ) - z‖⁻¹) := by
      rw [Real.log_inv, abs_of_neg (Real.log_neg hnpos hn1)]
    rw [hlog] at h1; linarith
  exact mul_le_mul_of_nonneg_right hlogbound (by positivity)

/-- **~½·n·(log n)²** for the undirected-cycle × marked-cycle-perm-pair class. -/
theorem undirectedCycleLogSqPermPairClass_counts_div_factorial_isEquivalent :
    (fun n : ℕ => (undirectedCycleLogSqPermPairClass.counts n : ℝ) / (n.factorial : ℝ)) ~[atTop]
      (fun n : ℕ => (1 / 2 : ℝ) * (n : ℝ) * (Real.log n) ^ 2) := by
  set R : ℝ := 2 with hR_def
  set φ : ℝ := Real.pi / 4 with hφ_def
  have hφ0 : 0 < φ := by rw [hφ_def]; positivity
  have hφ2 : φ < Real.pi / 2 := by rw [hφ_def]; linarith [Real.pi_pos]
  have hφπ : φ < Real.pi := by linarith [Real.pi_pos]
  have hsing : Tendsto
      (fun z : ℂ => ‖undirectedCycleLogSqPermPairFun z
          - (1 / 2 : ℂ) * logSqSingularityFun ((2 : ℝ) : ℂ) z‖ * ‖(1 : ℂ) - z‖ ^ (2 : ℝ)
        * ((Real.log (‖(1 : ℂ) - z‖⁻¹)) ^ 2)⁻¹)
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0) := by
    have hpoly : Tendsto (fun z : ℂ => ‖(1 / 2 : ℂ) * z + (1 / 4 : ℂ) * z ^ 2‖)
        (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 ‖(1 / 2 : ℂ) * 1 + (1 / 4 : ℂ) * 1 ^ 2‖) := by
      apply Tendsto.mono_left _ nhdsWithin_le_nhds
      exact (Continuous.norm (by fun_prop)).tendsto 1
    have hmul := hpoly.mul (negLog_over_logSq_tendsto_zero (R := R) (φ := φ))
    rw [mul_zero] at hmul
    refine hmul.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz_ne : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz.2.1)
    have hnz : ‖(1 : ℂ) - z‖ ≠ 0 := norm_ne_zero_iff.mpr hz_ne
    have hcpow : ‖logSingularityFun ((2 : ℝ) : ℂ) z‖ * ‖(1 : ℂ) - z‖ ^ (2 : ℝ)
        = ‖-Complex.log (1 - z)‖ := by
      have hr2 : ‖(1 : ℂ) - z‖ ^ (2 : ℝ) = ‖(1 : ℂ) - z‖ ^ 2 := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rw [logSingularityFun, show ((2 : ℝ) : ℂ) = (2 : ℂ) by norm_num, Complex.cpow_neg,
        show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast, norm_mul, norm_inv,
        norm_pow, hr2, mul_right_comm, inv_mul_cancel₀ (pow_ne_zero 2 hnz), one_mul]
    rw [undirectedCycleLogSqPermPairFun_residual, norm_mul,
      show ‖-((1 / 2 : ℂ) * z + (1 / 4 : ℂ) * z ^ 2)‖ = ‖(1 / 2 : ℂ) * z + (1 / 4 : ℂ) * z ^ 2‖
        from norm_neg _, ← hcpow]
    ring
  have htransfer := logSq_transfer_theorem_natural_remainder
    (α := (2 : ℝ)) (C := (1 / 2 : ℂ)) (R := R) (φ := φ)
    (f := undirectedCycleLogSqPermPairFun)
    (p := PowerSeries.toFMLS (PowerSeries.mapℂ undirectedCycleLogSqPermPairClass.egf))
    (by norm_num) (by norm_num) (by rw [hR_def]; norm_num) hφ0 hφ2
    undirectedCycleLogSqPermPairFun_hasFPowerSeriesAt
    (analyticOnNhd_undirectedCycleLogSqPermPairFun_deltaDomain hφ0 hφπ)
    hsing
  have hLHS : (fun n : ℕ =>
        (PowerSeries.toFMLS (PowerSeries.mapℂ undirectedCycleLogSqPermPairClass.egf)).coeff n)
      = (fun n : ℕ =>
          (((undirectedCycleLogSqPermPairClass.counts n : ℝ) / (n.factorial : ℝ) : ℝ) : ℂ)) := by
    funext n
    rw [PowerSeries.coeff_toFMLS, PowerSeries.coeff_mapℂ, CombClass.coeff_egf]
    push_cast; ring
  have hRHS : (fun n : ℕ => (1 / 2 : ℂ) *
        (((n : ℝ) ^ ((2 : ℝ) - 1) / Real.Gamma 2 * (Real.log n) ^ 2 : ℝ) : ℂ))
      = (fun n : ℕ => (((1 / 2 : ℝ) * (n : ℝ) * (Real.log n) ^ 2 : ℝ) : ℂ)) := by
    funext n
    rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.Gamma_two, div_one]
    push_cast; ring
  rw [hLHS, hRHS] at htransfer
  exact ofReal_isEquivalent_iff.mp htransfer

/-! ### This class genuinely NEEDS the natural transfer: the strong log² remainder fails.
Along the real radial path `z = 1 - 1/(n+2) → 1`, `‖R(z)‖·‖1-z‖² = ‖z/2+z²/4‖·log(n+2) → ∞`,
so `R` is not `o(|1-z|^{-2})` — the strong-remainder log² transfer cannot apply. -/

/-- Positive radial approach to the dominant singularity. -/
def radialSeq (n : ℕ) : ℂ :=
  (((1 : ℝ) - ((n : ℝ) + 2)⁻¹ : ℝ) : ℂ)

private lemma natCast_add_two_tendsto_atTop :
    Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro b
  have hb : ∀ᶠ n : ℕ in atTop, b - 2 ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (b - 2))
  filter_upwards [hb] with n hn
  linarith

lemma radialSeq_tendsto_one :
    Tendsto radialSeq atTop (𝓝 (1 : ℂ)) := by
  have hinv :
      Tendsto (fun n : ℕ => ((n : ℝ) + 2)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp natCast_add_two_tendsto_atTop
  have h0 :
      Tendsto (fun n : ℕ => (1 : ℝ) - ((n : ℝ) + 2)⁻¹) atTop (𝓝 (1 : ℝ)) := by
    simpa using tendsto_const_nhds.sub hinv
  have hC := (Complex.continuous_ofReal.tendsto (1 : ℝ)).comp h0
  simpa [radialSeq] using hC

private lemma radialSeq_norm (n : ℕ) :
    ‖radialSeq n‖ = 1 - ((n : ℝ) + 2)⁻¹ := by
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hxpos : 0 < (n : ℝ) + 2 := by linarith
  have hxone : (1 : ℝ) ≤ (n : ℝ) + 2 := by linarith
  have hinv_le_one : ((n : ℝ) + 2)⁻¹ ≤ 1 := by
    have hdiv : (1 : ℝ) / ((n : ℝ) + 2) ≤ 1 := by
      rw [div_le_one hxpos]
      exact hxone
    simpa [one_div] using hdiv
  have hnonneg : 0 ≤ 1 - ((n : ℝ) + 2)⁻¹ := by linarith
  rw [radialSeq, Complex.norm_real, Real.norm_of_nonneg hnonneg]

private lemma radialSeq_mem_delta (n : ℕ) :
    radialSeq n ∈ DeltaDomainArg 2 (Real.pi / 4) := by
  let r : ℝ := 1 - ((n : ℝ) + 2)⁻¹
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hxpos : 0 < (n : ℝ) + 2 := by linarith
  have hinvpos : 0 < ((n : ℝ) + 2)⁻¹ := inv_pos.mpr hxpos
  have hr1 : r < 1 := by
    dsimp [r]
    linarith
  have hrR : r < (2 : ℝ) := by linarith
  have hφ0 : 0 < Real.pi / 4 := by positivity
  have hφ2 : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  have hmem : radialSeq n ∈ Metric.closedBall (0 : ℂ) r := by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, radialSeq_norm]
  exact closedBall_subset_deltaDomain
    (R := (2 : ℝ)) (φ := Real.pi / 4) (r := r) hr1 hrR hφ0 hφ2 hmem

lemma radialSeq_mem_delta_eventually :
    ∀ᶠ n : ℕ in atTop, radialSeq n ∈ DeltaDomainArg 2 (Real.pi / 4) :=
  Eventually.of_forall radialSeq_mem_delta

lemma radialSeq_tendsto_delta :
    Tendsto radialSeq atTop (𝓝[DeltaDomainArg 2 (Real.pi / 4)] (1 : ℂ)) := by
  rw [tendsto_nhdsWithin_iff]
  exact ⟨radialSeq_tendsto_one, radialSeq_mem_delta_eventually⟩

private lemma radialSeq_one_sub (n : ℕ) :
    (1 : ℂ) - radialSeq n = (((n : ℝ) + 2)⁻¹ : ℂ) := by
  simp [radialSeq]

private lemma radialSeq_logSingularity_norm_mul (n : ℕ) :
    ‖logSingularityFun ((2 : ℝ) : ℂ) (radialSeq n)‖ *
        ‖(1 : ℂ) - radialSeq n‖ ^ (2 : ℝ)
      =
    Real.log ((n : ℝ) + 2) := by
  set x : ℝ := (n : ℝ) + 2 with hxdef
  set t : ℝ := x⁻¹ with htdef
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hxpos : 0 < x := by
    rw [hxdef]
    linarith
  have hxone : (1 : ℝ) ≤ x := by
    rw [hxdef]
    linarith
  have htpos : 0 < t := by
    rw [htdef]
    exact inv_pos.mpr hxpos
  have htne : t ≠ 0 := ne_of_gt htpos
  have h1z : (1 : ℂ) - radialSeq n = (t : ℂ) := by
    rw [htdef, hxdef, radialSeq_one_sub n]; push_cast; ring
  have hnorm1z : ‖(1 : ℂ) - radialSeq n‖ = t := by
    rw [h1z, Complex.norm_real, Real.norm_of_nonneg htpos.le]
  have hrpow : ‖(1 : ℂ) - radialSeq n‖ ^ (2 : ℝ) = t ^ 2 := by
    rw [hnorm1z, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hlogeq : -Complex.log (t : ℂ) = (Real.log x : ℂ) := by
    have hlogt : Complex.log (t : ℂ) = (Real.log t : ℂ) := by
      simpa using (Complex.ofReal_log htpos.le).symm
    rw [hlogt, ← Complex.ofReal_neg]
    congr 1
    rw [htdef, Real.log_inv]
    ring
  have hlogx_nonneg : 0 ≤ Real.log x := Real.log_nonneg hxone
  have hlognorm : ‖-Complex.log (t : ℂ)‖ = Real.log x := by
    rw [hlogeq, Complex.norm_real, Real.norm_of_nonneg hlogx_nonneg]
  have hpow_norm : ‖(t : ℂ) ^ (-(((2 : ℝ) : ℂ)))‖ = (t ^ 2)⁻¹ := by
    rw [show ((2 : ℝ) : ℂ) = (2 : ℂ) by norm_num, Complex.cpow_neg,
      show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast, norm_inv, norm_pow,
      Complex.norm_real, Real.norm_of_nonneg htpos.le]
  calc
    ‖logSingularityFun ((2 : ℝ) : ℂ) (radialSeq n)‖ *
        ‖(1 : ℂ) - radialSeq n‖ ^ (2 : ℝ)
        =
      ((t ^ 2)⁻¹ * Real.log x) * t ^ 2 := by
        rw [logSingularityFun, hrpow, h1z, norm_mul, hpow_norm, hlognorm]
    _ = Real.log x := by
        field_simp [htne]
    _ = Real.log ((n : ℝ) + 2) := by rw [hxdef]

private lemma logSqResidual_strongScale_radialSeq_eq (n : ℕ) :
    ‖undirectedCycleLogSqPermPairFun (radialSeq n)
        - (1 / 2 : ℂ) * logSqSingularityFun ((2 : ℝ) : ℂ) (radialSeq n)‖
      * ‖(1 : ℂ) - radialSeq n‖ ^ (2 : ℝ)
      =
    ‖(1 / 2 : ℂ) * radialSeq n + (1 / 4 : ℂ) * (radialSeq n) ^ 2‖
      * Real.log ((n : ℝ) + 2) := by
  have hlog := radialSeq_logSingularity_norm_mul n
  rw [undirectedCycleLogSqPermPairFun_residual (radialSeq n), norm_mul, norm_neg,
    mul_assoc, hlog]

theorem logSqResidual_strongScale_radialSeq_tendsto_atTop :
    Tendsto
      (fun n : ℕ =>
        ‖undirectedCycleLogSqPermPairFun (radialSeq n)
            - (1 / 2 : ℂ) * logSqSingularityFun ((2 : ℝ) : ℂ) (radialSeq n)‖
          * ‖(1 : ℂ) - radialSeq n‖ ^ (2 : ℝ))
      atTop atTop := by
  have hpoly :
      Tendsto
        (fun n : ℕ =>
          ‖(1 / 2 : ℂ) * radialSeq n + (1 / 4 : ℂ) * (radialSeq n) ^ 2‖)
        atTop (𝓝 (3 / 4 : ℝ)) := by
    have hcont :
        Continuous fun z : ℂ => ‖(1 / 2 : ℂ) * z + (1 / 4 : ℂ) * z ^ 2‖ := by
      fun_prop
    have heq : (3 / 4 : ℝ)
        = ‖(1 / 2 : ℂ) * (1 : ℂ) + (1 / 4 : ℂ) * (1 : ℂ) ^ 2‖ := by
      rw [show (1 / 2 : ℂ) * (1 : ℂ) + (1 / 4 : ℂ) * (1 : ℂ) ^ 2 = ((3 / 4 : ℝ) : ℂ) by
        push_cast; ring, Complex.norm_real, Real.norm_of_nonneg (by norm_num)]
    rw [heq]
    exact (hcont.tendsto (1 : ℂ)).comp radialSeq_tendsto_one
  have hpoly_ge :
      ∀ᶠ n : ℕ in atTop,
        (1 / 2 : ℝ) ≤
          ‖(1 / 2 : ℂ) * radialSeq n + (1 / 4 : ℂ) * (radialSeq n) ^ 2‖ := by
    have hgt :
        ∀ᶠ n : ℕ in atTop,
          (1 / 2 : ℝ) <
            ‖(1 / 2 : ℂ) * radialSeq n + (1 / 4 : ℂ) * (radialSeq n) ^ 2‖ :=
      hpoly.eventually (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 3 / 4))
    exact hgt.mono fun _ hn => le_of_lt hn
  have hlog :
      Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 2)) atTop atTop :=
    Real.tendsto_log_atTop.comp natCast_add_two_tendsto_atTop
  have hhalf_log :
      Tendsto (fun n : ℕ => (1 / 2 : ℝ) * Real.log ((n : ℝ) + 2)) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    have hb :
        ∀ᶠ n : ℕ in atTop, 2 * b ≤ Real.log ((n : ℝ) + 2) :=
      hlog.eventually (eventually_ge_atTop (2 * b))
    filter_upwards [hb] with n hn
    nlinarith
  have hprod :
      Tendsto
        (fun n : ℕ =>
          ‖(1 / 2 : ℂ) * radialSeq n + (1 / 4 : ℂ) * (radialSeq n) ^ 2‖
            * Real.log ((n : ℝ) + 2))
        atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    have hb :
        ∀ᶠ n : ℕ in atTop, b ≤ (1 / 2 : ℝ) * Real.log ((n : ℝ) + 2) :=
      hhalf_log.eventually (eventually_ge_atTop b)
    filter_upwards [hb, hpoly_ge] with n hb hge
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
    have hlog_nonneg : 0 ≤ Real.log ((n : ℝ) + 2) := by
      apply Real.log_nonneg
      linarith
    calc
      b ≤ (1 / 2 : ℝ) * Real.log ((n : ℝ) + 2) := hb
      _ ≤ ‖(1 / 2 : ℂ) * radialSeq n + (1 / 4 : ℂ) * (radialSeq n) ^ 2‖
            * Real.log ((n : ℝ) + 2) :=
          mul_le_mul_of_nonneg_right hge hlog_nonneg
  refine hprod.congr' ?_
  filter_upwards with n
  exact (logSqResidual_strongScale_radialSeq_eq n).symm

theorem logSqResidual_not_strong_remainder :
    ¬ Tendsto
      (fun z : ℂ =>
        ‖undirectedCycleLogSqPermPairFun z
            - (1 / 2 : ℂ) * logSqSingularityFun ((2 : ℝ) : ℂ) z‖
          * ‖(1 : ℂ) - z‖ ^ (2 : ℝ))
      (𝓝[DeltaDomainArg 2 (Real.pi / 4)] (1 : ℂ)) (𝓝 0) := by
  intro hstrong
  have hseq_zero :
      Tendsto
        (fun n : ℕ =>
          ‖undirectedCycleLogSqPermPairFun (radialSeq n)
              - (1 / 2 : ℂ) * logSqSingularityFun ((2 : ℝ) : ℂ) (radialSeq n)‖
            * ‖(1 : ℂ) - radialSeq n‖ ^ (2 : ℝ))
        atTop (𝓝 0) :=
    hstrong.comp radialSeq_tendsto_delta
  have hseq_atTop := logSqResidual_strongScale_radialSeq_tendsto_atTop
  have hsmall :
      ∀ᶠ n : ℕ in atTop,
        ‖undirectedCycleLogSqPermPairFun (radialSeq n)
            - (1 / 2 : ℂ) * logSqSingularityFun ((2 : ℝ) : ℂ) (radialSeq n)‖
          * ‖(1 : ℂ) - radialSeq n‖ ^ (2 : ℝ) < 1 :=
    hseq_zero.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hlarge :
      ∀ᶠ n : ℕ in atTop,
        1 ≤
        ‖undirectedCycleLogSqPermPairFun (radialSeq n)
            - (1 / 2 : ℂ) * logSqSingularityFun ((2 : ℝ) : ℂ) (radialSeq n)‖
          * ‖(1 : ℂ) - radialSeq n‖ ^ (2 : ℝ) :=
    hseq_atTop.eventually (eventually_ge_atTop (1 : ℝ))
  obtain ⟨n, hs, hl⟩ := (hsmall.and hlarge).exists
  linarith

end AnalyticCombinatorics
