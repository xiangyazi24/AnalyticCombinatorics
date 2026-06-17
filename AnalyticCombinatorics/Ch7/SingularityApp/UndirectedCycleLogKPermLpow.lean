import AnalyticCombinatorics.Ch7.SingularityApp.CycleMarkedPermLpow
import AnalyticCombinatorics.Ch7.SingularityApp.UndirectedCycleMarkedPermPairs

/-!
# Undirected cycles times marked-cycle permutation `k`-tuples

`undirectedCycleLogKPermLpowClass k := undirectedCycleClass ⋆ cycleMarkedPermLpowClass k`
has EGF

  `(1/2 * log(1/(1-z)) - z/2 - z^2/4) * (1-z)^{-k} * log(1/(1-z))^k`

so its dominant term is

  `1/2 * (1-z)^{-k} * (-log(1-z))^{k+1}`.

The residual is a natural log-remainder, giving

  `a_n / n! ~ 1/2 * n^{k-1}/(k-1)! * (log n)^{k+1}`.
-/

open Complex Filter Asymptotics
open scoped BigOperators PowerSeries Topology

noncomputable section

namespace AnalyticCombinatorics

open AnalyticCombinatorics.Ch1
open AnalyticCombinatorics.Ch5.Meromorphic.Alignments

/-- Undirected cycle ⋆ `k` marked-cycle permutations. -/
def undirectedCycleLogKPermLpowClass (k : ℕ) : CombClass :=
  TwoRegularClass.undirectedCycleClass.lprod (cycleMarkedPermLpowClass k)

theorem mapℂ_undirectedCycleLogKPermLpowClass_egf {k : ℕ} (hk : 1 ≤ k) :
    PowerSeries.mapℂ (undirectedCycleLogKPermLpowClass k).egf
      = TwoRegularClass.twoRegularCoreEGFℂ * logKGF (k : ℂ) k := by
  rw [undirectedCycleLogKPermLpowClass, CombClass.egf_lprod, map_mul,
    mapℂ_cycleMarkedPermLpowClass_egf hk, TwoRegularClass.twoRegularCoreEGFℂ]

/-- Analytic carrier `twoRegularCoreFun(z) * logKSingularityFun k k z`. -/
def undirectedCycleLogKPermLpowFun (k : ℕ) (z : ℂ) : ℂ :=
  TwoRegularClass.twoRegularCoreFun z * logKSingularityFun ((k : ℝ) : ℂ) k z

/-- `twoRegularCoreFun` is `Δ`-analytic. -/
lemma analyticOnNhd_twoRegularCoreFun_deltaDomain_logK {R φ : ℝ} (hφ0 : 0 < φ) :
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

lemma analyticOnNhd_undirectedCycleLogKPermLpowFun_deltaDomain {k : ℕ} {R φ : ℝ}
    (hφ0 : 0 < φ) (hφπ : φ < Real.pi) :
    AnalyticOnNhd ℂ (undirectedCycleLogKPermLpowFun k) (DeltaDomainArg R φ) := by
  simpa [undirectedCycleLogKPermLpowFun] using
    (analyticOnNhd_twoRegularCoreFun_deltaDomain_logK (R := R) (φ := φ) hφ0).mul
      (analyticOnNhd_logKSingularityFun_deltaDomain (α := ((k : ℝ) : ℂ)) k hφ0 hφπ)

/-- Faithfulness: power series of the carrier is `mapℂ A.egf`. -/
lemma undirectedCycleLogKPermLpowFun_hasFPowerSeriesAt {k : ℕ} (hk : 1 ≤ k) :
    HasFPowerSeriesAt (undirectedCycleLogKPermLpowFun k)
      (PowerSeries.toFMLS (PowerSeries.mapℂ (undirectedCycleLogKPermLpowClass k).egf)) 0 := by
  rw [hasFPowerSeriesAt_iff]
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with z hz
  have hz_norm : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hz
  have hlogModel := logKGF_hasSum (α := ((k : ℝ) : ℂ)) (z := z) hz_norm k
  have hprod := hasSum_powerSeries_mul TwoRegularClass.twoRegularCoreEGFℂ
    (logKGF ((k : ℝ) : ℂ) k)
    (twoRegularCore_hasSum hz_norm) hlogModel
    (twoRegularCore_summable_norm hz_norm)
    (logKGF_summable_norm (α := ((k : ℝ) : ℂ)) (z := z) hz_norm k)
  have hkcast : ((k : ℝ) : ℂ) = (k : ℂ) := by push_cast; ring
  rw [hkcast, ← mapℂ_undirectedCycleLogKPermLpowClass_egf hk] at hprod
  have hval : TwoRegularClass.twoRegularCoreFun z
        * ((1 - z) ^ (-(k : ℂ)) * (-Complex.log (1 - z)) ^ k)
      = undirectedCycleLogKPermLpowFun k z := by
    rw [undirectedCycleLogKPermLpowFun, logKSingularityFun, hkcast]
  rw [hval] at hprod
  simpa [PowerSeries.coeff_toFMLS, smul_eq_mul, mul_comm] using hprod

/-- The residual identity for the `log^{k+1}` model. -/
lemma undirectedCycleLogKPermLpowFun_residual (k : ℕ) (z : ℂ) :
    undirectedCycleLogKPermLpowFun k z
        - (1 / 2 : ℂ) * logKSingularityFun ((k : ℝ) : ℂ) (k + 1) z
      = -((1 / 2 : ℂ) * z + (1 / 4 : ℂ) * z ^ 2)
          * logKSingularityFun ((k : ℝ) : ℂ) k z := by
  simp only [undirectedCycleLogKPermLpowFun, TwoRegularClass.twoRegularCoreFun, cycleAnalyticFun,
    logKSingularityFun, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [pow_succ]
  ring

private lemma logKsucc_ratio_atTop_tendsto_zero (k : ℕ) :
    Tendsto (fun L : ℝ => (L + Real.pi) ^ k * (L ^ (k + 1))⁻¹) atTop (𝓝 0) := by
  have hratio : Tendsto (fun L : ℝ => (L + Real.pi) / L) atTop (𝓝 (1 : ℝ)) := by
    have hpi : Tendsto (fun L : ℝ => Real.pi * L⁻¹) atTop (𝓝 (0 : ℝ)) := by
      simpa using
        (tendsto_inv_atTop_zero.const_mul Real.pi :
          Tendsto (fun L : ℝ => Real.pi * L⁻¹) atTop (𝓝 (Real.pi * 0)))
    have heq : (fun L : ℝ => (L + Real.pi) / L)
        =ᶠ[atTop] (fun L : ℝ => 1 + Real.pi * L⁻¹) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
      field_simp [hL.ne']
    rw [tendsto_congr' heq]
    simpa using tendsto_const_nhds.add hpi
  have hpow : Tendsto (fun L : ℝ => ((L + Real.pi) / L) ^ k) atTop (𝓝 (1 : ℝ)) := by
    simpa using hratio.pow k
  have hinv : Tendsto (fun L : ℝ => L⁻¹) atTop (𝓝 (0 : ℝ)) := tendsto_inv_atTop_zero
  have hprod : Tendsto (fun L : ℝ => ((L + Real.pi) / L) ^ k * L⁻¹) atTop (𝓝 (0 : ℝ)) := by
    simpa using hpow.mul hinv
  have heq : (fun L : ℝ => (L + Real.pi) ^ k * (L ^ (k + 1))⁻¹)
      =ᶠ[atTop] (fun L : ℝ => ((L + Real.pi) / L) ^ k * L⁻¹) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    have hLne : L ≠ 0 := hL.ne'
    rw [div_pow, pow_succ]
    field_simp [hLne]
  exact hprod.congr' heq.symm

/-- `‖-log(1-z)‖^k / log^{k+1}(1/‖1-z‖) → 0` near `1`. -/
lemma negLogPow_over_logKsucc_tendsto_zero {R φ : ℝ} (k : ℕ) :
    Tendsto
      (fun z : ℂ =>
        ‖-Complex.log (1 - z)‖ ^ k
          * ((Real.log (‖(1 : ℂ) - z‖⁻¹)) ^ (k + 1))⁻¹)
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0) := by
  have hnorm0 : Tendsto (fun z : ℂ => ‖(1 : ℂ) - z‖)
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    have h : Continuous (fun z : ℂ => ‖(1 : ℂ) - z‖) := by fun_prop
    simpa using h.tendsto 1
  have hLatTop : Tendsto (fun z : ℂ => Real.log (‖(1 : ℂ) - z‖⁻¹))
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) atTop := by
    have hinv : Tendsto (fun z : ℂ => ‖(1 : ℂ) - z‖⁻¹)
        (𝓝[DeltaDomainArg R φ] (1 : ℂ)) atTop := by
      apply Filter.Tendsto.comp tendsto_inv_nhdsGT_zero
      rw [tendsto_nhdsWithin_iff]
      refine ⟨hnorm0, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hz.2.1))
    exact Real.tendsto_log_atTop.comp hinv
  have hub : Tendsto
      (fun z : ℂ =>
        (Real.log (‖(1 : ℂ) - z‖⁻¹) + Real.pi) ^ k
          * ((Real.log (‖(1 : ℂ) - z‖⁻¹)) ^ (k + 1))⁻¹)
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0) :=
    (logKsucc_ratio_atTop_tendsto_zero k).comp hLatTop
  have hnonneg :
      ∀ᶠ z : ℂ in 𝓝[DeltaDomainArg R φ] (1 : ℂ),
        0 ≤ ‖-Complex.log (1 - z)‖ ^ k
          * ((Real.log (‖(1 : ℂ) - z‖⁻¹)) ^ (k + 1))⁻¹ := by
    filter_upwards [hLatTop.eventually_gt_atTop (0 : ℝ)] with z hLpos
    exact mul_nonneg (pow_nonneg (norm_nonneg _) k)
      (inv_nonneg.mpr (pow_nonneg hLpos.le (k + 1)))
  refine squeeze_zero' hnonneg ?_ hub
  filter_upwards [hnorm0.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    self_mem_nhdsWithin] with z hz1 hzΔ
  have hz_ne : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hzΔ.2.1)
  have hnpos : 0 < ‖(1 : ℂ) - z‖ := norm_pos_iff.mpr hz_ne
  have hn1 : ‖(1 : ℂ) - z‖ < 1 := by
    simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using hz1
  have hLpos : 0 < Real.log (‖(1 : ℂ) - z‖⁻¹) := by
    rw [Real.log_inv]
    have := Real.log_neg hnpos hn1
    linarith
  have hlogbound : ‖-Complex.log (1 - z)‖
      ≤ Real.log (‖(1 : ℂ) - z‖⁻¹) + Real.pi := by
    rw [norm_neg]
    have h1 : ‖Complex.log (1 - z)‖
        ≤ |(Complex.log (1 - z)).re| + |(Complex.log (1 - z)).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    rw [Complex.log_re, Complex.log_im] at h1
    have harg : |Complex.arg (1 - z)| ≤ Real.pi := Complex.abs_arg_le_pi _
    have hlog : |Real.log ‖(1 : ℂ) - z‖|
        = Real.log (‖(1 : ℂ) - z‖⁻¹) := by
      rw [Real.log_inv, abs_of_neg (Real.log_neg hnpos hn1)]
    rw [hlog] at h1
    linarith
  have hpowbound : ‖-Complex.log (1 - z)‖ ^ k
      ≤ (Real.log (‖(1 : ℂ) - z‖⁻¹) + Real.pi) ^ k :=
    pow_le_pow_left₀ (norm_nonneg _) hlogbound k
  exact mul_le_mul_of_nonneg_right hpowbound
    (inv_nonneg.mpr (pow_nonneg hLpos.le (k + 1)))

/-- **~½·n^{k-1}/(k-1)!·(log n)^{k+1}** for the undirected-cycle product class. -/
theorem undirectedCycleLogKPermLpowClass_counts_div_factorial_isEquivalent {k : ℕ}
    (hk : 2 ≤ k) :
    (fun n : ℕ => ((undirectedCycleLogKPermLpowClass k).counts n : ℝ) / (n.factorial : ℝ))
      ~[atTop]
    (fun n : ℕ =>
      (1 / 2 : ℝ) * (n : ℝ) ^ (k - 1) / ((k - 1).factorial : ℝ)
        * (Real.log n) ^ (k + 1)) := by
  set R : ℝ := 2 with hR_def
  set φ : ℝ := Real.pi / 4 with hφ_def
  have hk1 : 1 ≤ k := by omega
  have hksucc1 : 1 ≤ k + 1 := by omega
  have hkR : (1 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 1 < k)
  have hφ0 : 0 < φ := by rw [hφ_def]; positivity
  have hφ2 : φ < Real.pi / 2 := by rw [hφ_def]; linarith [Real.pi_pos]
  have hφπ : φ < Real.pi := by linarith [Real.pi_pos]
  have hsing : Tendsto
      (fun z : ℂ => ‖undirectedCycleLogKPermLpowFun k z
          - (1 / 2 : ℂ) * logKSingularityFun ((k : ℝ) : ℂ) (k + 1) z‖
          * ‖(1 : ℂ) - z‖ ^ (k : ℝ)
        * ((Real.log (‖(1 : ℂ) - z‖⁻¹)) ^ (k + 1))⁻¹)
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0) := by
    have hpoly : Tendsto (fun z : ℂ => ‖(1 / 2 : ℂ) * z + (1 / 4 : ℂ) * z ^ 2‖)
        (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 ‖(1 / 2 : ℂ) * 1 + (1 / 4 : ℂ) * 1 ^ 2‖) := by
      apply Tendsto.mono_left _ nhdsWithin_le_nhds
      exact (Continuous.norm (by fun_prop)).tendsto 1
    have hmul := hpoly.mul (negLogPow_over_logKsucc_tendsto_zero (R := R) (φ := φ) k)
    rw [mul_zero] at hmul
    refine hmul.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz_ne : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz.2.1)
    have hnz : ‖(1 : ℂ) - z‖ ≠ 0 := norm_ne_zero_iff.mpr hz_ne
    have hcpow : ‖logKSingularityFun ((k : ℝ) : ℂ) k z‖ * ‖(1 : ℂ) - z‖ ^ (k : ℝ)
        = ‖-Complex.log (1 - z)‖ ^ k := by
      have hrk : ‖(1 : ℂ) - z‖ ^ (k : ℝ) = ‖(1 : ℂ) - z‖ ^ k := by
        rw [show (k : ℝ) = ((k : ℕ) : ℝ) by rfl, Real.rpow_natCast]
      rw [logKSingularityFun, show ((k : ℝ) : ℂ) = (k : ℂ) by push_cast; ring,
        Complex.cpow_neg, show (k : ℂ) = ((k : ℕ) : ℂ) by rfl, Complex.cpow_natCast,
        norm_mul, norm_inv, norm_pow, hrk, mul_right_comm,
        inv_mul_cancel₀ (pow_ne_zero k hnz), one_mul]
      rw [norm_pow]
    rw [undirectedCycleLogKPermLpowFun_residual k z, norm_mul,
      show ‖-((1 / 2 : ℂ) * z + (1 / 4 : ℂ) * z ^ 2)‖
          = ‖(1 / 2 : ℂ) * z + (1 / 4 : ℂ) * z ^ 2‖ from norm_neg _, ← hcpow]
    ring
  have htransfer := logK_transfer_theorem_natural_remainder
    (α := (k : ℝ)) (C := (1 / 2 : ℂ)) (R := R) (φ := φ)
    (f := undirectedCycleLogKPermLpowFun k)
    (p := PowerSeries.toFMLS (PowerSeries.mapℂ (undirectedCycleLogKPermLpowClass k).egf))
    hkR (by norm_num) (by rw [hR_def]; norm_num) hφ0 hφ2 (k + 1) hksucc1
    (undirectedCycleLogKPermLpowFun_hasFPowerSeriesAt hk1)
    (analyticOnNhd_undirectedCycleLogKPermLpowFun_deltaDomain (k := k) hφ0 hφπ)
    hsing
  have hLHS : (fun n : ℕ =>
        (PowerSeries.toFMLS (PowerSeries.mapℂ (undirectedCycleLogKPermLpowClass k).egf)).coeff n)
      = (fun n : ℕ =>
          (((((undirectedCycleLogKPermLpowClass k).counts n : ℝ) / (n.factorial : ℝ)) : ℝ) : ℂ)) := by
    funext n
    rw [PowerSeries.coeff_toFMLS, PowerSeries.coeff_mapℂ, CombClass.coeff_egf]
    push_cast; ring
  have hRHS : (fun n : ℕ => (1 / 2 : ℂ) *
        (((n : ℝ) ^ ((k : ℝ) - 1) / Real.Gamma (k : ℝ)
            * (Real.log n) ^ (k + 1) : ℝ) : ℂ))
      = (fun n : ℕ =>
          ((((1 / 2 : ℝ) * (n : ℝ) ^ (k - 1) / ((k - 1).factorial : ℝ)
              * (Real.log n) ^ (k + 1)) : ℝ) : ℂ)) := by
    funext n
    have hΓ : Real.Gamma (k : ℝ) = ((k - 1).factorial : ℝ) := by
      have hkk : (k : ℝ) = ((k - 1 : ℕ) : ℝ) + 1 := by
        have : k - 1 + 1 = k := by omega
        rw [← this]
        push_cast
        ring
      rw [hkk, Real.Gamma_nat_eq_factorial]
    have hpow : ((n : ℝ) ^ ((k : ℝ) - 1)) = (n : ℝ) ^ (k - 1) := by
      have hkk : ((k : ℝ) - 1) = (((k - 1 : ℕ)) : ℝ) := by
        have : k - 1 + 1 = k := by omega
        rw [show ((k : ℝ) - 1) = ((k : ℝ)) - 1 from rfl]
        rw [show (((k - 1 : ℕ)) : ℝ) = (k : ℝ) - 1 by
          rw [← this]
          push_cast
          ring]
      rw [hkk, Real.rpow_natCast]
    rw [hΓ, hpow]
    push_cast
    ring
  rw [hLHS, hRHS] at htransfer
  exact ofReal_isEquivalent_iff.mp htransfer

end AnalyticCombinatorics
