import AnalyticCombinatorics.Ch7.SingularityApp.UndirectedCycleMarkedPermPairs
import AnalyticCombinatorics.Ch7.SingularityApp.CycleMarkedPermTuple

/-!
# Undirected-cycle-marked permutation `k`-tuples — the natural remainder at every integer α

This generalizes `UndirectedCycleMarkedPermPairs` (k = 2) to the integer family

  `A k := undirectedCycleClass ⋆ permutations^{⋆k}`,

a `k`-tuple of permutations carrying one distinguished undirected cycle of length ≥ 3,
with EGF

  `(½·log(1/(1-z)) - z/2 - z²/4)·(1-z)^{-k}`
    `= ½·(1-z)^{-k}(-log(1-z)) - (z/2 + z²/4)(1-z)^{-k}`.

For every `k ≥ 2` the residual `-(z/2+z²/4)(1-z)^{-k}` has `‖·‖·‖1-z‖^k → 3/4 ≠ 0`
(strong-remainder transfer fails) but `/log(1/‖1-z‖) → 0` (natural-remainder transfer
applies), giving

  `aₙ / n! ~ ½ · n^{k-1}/(k-1)! · log n`.

So the natural-remainder transfer is needed at *every* integer exponent, not just α = 2.
-/

open Complex Filter Asymptotics
open scoped BigOperators PowerSeries Topology

noncomputable section

namespace AnalyticCombinatorics

open AnalyticCombinatorics.Ch1
open AnalyticCombinatorics.Ch5.Meromorphic.Alignments

/-- A `k`-tuple of permutations with a distinguished undirected cycle (length ≥ 3). -/
def undirectedCycleMarkedPermTupleClass (k : ℕ) : CombClass :=
  TwoRegularClass.undirectedCycleClass.lprod (CombClass.permutations.lpow k)

theorem mapℂ_undirectedCycleMarkedPermTupleClass_egf {k : ℕ} (hk : 1 ≤ k) :
    PowerSeries.mapℂ (undirectedCycleMarkedPermTupleClass k).egf
      = TwoRegularClass.twoRegularCoreEGFℂ * oneSubCpowGF (k : ℂ) := by
  rw [undirectedCycleMarkedPermTupleClass, CombClass.egf_lprod, CombClass.egf_lpow, map_mul,
    map_pow, mapℂ_permutations_egf_pow hk, TwoRegularClass.twoRegularCoreEGFℂ]

/-- Analytic representative `twoRegularCoreFun(z)·(1-z)^{-k}`. -/
def undirectedCycleMarkedPermTupleFun (k : ℕ) (z : ℂ) : ℂ :=
  TwoRegularClass.twoRegularCoreFun z * (1 - z) ^ (-(k : ℂ))

lemma undirectedCycleMarkedPermTupleFun_hasFPowerSeriesAt {k : ℕ} (hk : 1 ≤ k) :
    HasFPowerSeriesAt (undirectedCycleMarkedPermTupleFun k)
      (PowerSeries.toFMLS (PowerSeries.mapℂ (undirectedCycleMarkedPermTupleClass k).egf)) 0 := by
  rw [hasFPowerSeriesAt_iff]
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with z hz
  have hz_norm : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hz
  have hprod := hasSum_powerSeries_mul TwoRegularClass.twoRegularCoreEGFℂ (oneSubCpowGF (k : ℂ))
    (twoRegularCore_hasSum hz_norm)
    (oneSubCpowGF_hasSum (α := (k : ℂ)) (z := z) hz_norm)
    (twoRegularCore_summable_norm hz_norm)
    (oneSubCpowGF_summable_norm (α := (k : ℂ)) (z := z) hz_norm)
  rw [mapℂ_undirectedCycleMarkedPermTupleClass_egf hk]
  simpa [undirectedCycleMarkedPermTupleFun, PowerSeries.coeff_toFMLS, smul_eq_mul, mul_comm]
    using hprod

lemma analyticOnNhd_undirectedCycleMarkedPermTupleFun_deltaDomain {k : ℕ} {R φ : ℝ}
    (hφ0 : 0 < φ) (hφπ : φ < Real.pi) :
    AnalyticOnNhd ℂ (undirectedCycleMarkedPermTupleFun k) (DeltaDomainArg R φ) := by
  have hcpow : AnalyticOnNhd ℂ (fun z : ℂ => (1 - z) ^ (-(k : ℂ))) (DeltaDomainArg R φ) :=
    analyticOnNhd_one_sub_cpow_deltaDomain (α := (k : ℂ)) hφ0 hφπ
  have hfeq : undirectedCycleMarkedPermTupleFun k
      = fun z : ℂ => (1 / 2 : ℂ) * logSingularityFun ((k : ℝ) : ℂ) z
          - ((1 / 2 : ℂ) * z + (1 / 4 : ℂ) * z ^ 2) * (1 - z) ^ (-(k : ℂ)) := by
    funext z
    simp only [undirectedCycleMarkedPermTupleFun, TwoRegularClass.twoRegularCoreFun,
      cycleAnalyticFun, logSingularityFun, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [show (((k : ℝ) : ℂ)) = (k : ℂ) by norm_num]
    ring
  rw [hfeq]
  have hlog : AnalyticOnNhd ℂ (logSingularityFun ((k : ℝ) : ℂ)) (DeltaDomainArg R φ) :=
    analyticOnNhd_logSingularityFun_deltaDomain hφ0 hφπ
  have hpoly : AnalyticOnNhd ℂ (fun z : ℂ => (1 / 2 : ℂ) * z + (1 / 4 : ℂ) * z ^ 2)
      (DeltaDomainArg R φ) :=
    (analyticOnNhd_const.mul analyticOnNhd_id).add
      (analyticOnNhd_const.mul (analyticOnNhd_id.pow 2))
  exact (analyticOnNhd_const.mul hlog).sub (hpoly.mul hcpow)

/-- **Natural-remainder asymptotic for every integer `k ≥ 2`**: `aₙ/n! ~ ½·n^{k-1}/(k-1)!·log n`. -/
theorem undirectedCycleMarkedPermTupleClass_counts_div_factorial_isEquivalent {k : ℕ} (hk : 2 ≤ k) :
    (fun n : ℕ => ((undirectedCycleMarkedPermTupleClass k).counts n : ℝ) / (n.factorial : ℝ))
      ~[atTop] (fun n : ℕ => (1 / 2 : ℝ) * ((n : ℝ) ^ (k - 1) / ((k - 1).factorial : ℝ))
        * Real.log n) := by
  have hkR : (1 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hk1 : 1 ≤ k := by omega
  set R : ℝ := 2 with hR_def
  set φ : ℝ := Real.pi / 4 with hφ_def
  have hφ0 : 0 < φ := by rw [hφ_def]; positivity
  have hφ2 : φ < Real.pi / 2 := by rw [hφ_def]; linarith [Real.pi_pos]
  have hφπ : φ < Real.pi := by linarith [Real.pi_pos]
  have hsing : Tendsto
      (fun z : ℂ => ‖undirectedCycleMarkedPermTupleFun k z
          - (1 / 2 : ℂ) * logSingularityFun ((k : ℝ) : ℂ) z‖
        * ‖(1 : ℂ) - z‖ ^ (k : ℝ) * (Real.log (‖(1 : ℂ) - z‖⁻¹))⁻¹)
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0) := by
    have hEq : ∀ z ∈ DeltaDomainArg R φ,
        ‖undirectedCycleMarkedPermTupleFun k z - (1 / 2 : ℂ) * logSingularityFun ((k : ℝ) : ℂ) z‖
            * ‖(1 : ℂ) - z‖ ^ (k : ℝ) * (Real.log (‖(1 : ℂ) - z‖⁻¹))⁻¹
          = ‖(1 / 2 : ℂ) * z + (1 / 4 : ℂ) * z ^ 2‖ * (Real.log (‖(1 : ℂ) - z‖⁻¹))⁻¹ := by
      intro z hz
      have hz1 : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz.2.1)
      have hnz : ‖(1 : ℂ) - z‖ ≠ 0 := by rwa [norm_ne_zero_iff]
      have hg : undirectedCycleMarkedPermTupleFun k z
          - (1 / 2 : ℂ) * logSingularityFun ((k : ℝ) : ℂ) z
          = -((1 / 2 : ℂ) * z + (1 / 4 : ℂ) * z ^ 2) * ((1 - z) ^ k)⁻¹ := by
        have hcpow : (1 - z) ^ (-(k : ℂ)) = ((1 - z) ^ k)⁻¹ := by
          rw [show (-(k : ℂ)) = (((-k : ℤ)) : ℂ) by push_cast; ring, Complex.cpow_intCast,
            zpow_neg, zpow_natCast]
        simp only [undirectedCycleMarkedPermTupleFun, TwoRegularClass.twoRegularCoreFun,
          cycleAnalyticFun, logSingularityFun, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
          Complex.ofReal_natCast, hcpow]
        field_simp
        ring
      have hr2 : ‖(1 : ℂ) - z‖ ^ (k : ℝ) = ‖(1 : ℂ) - z‖ ^ k := by
        rw [← Real.rpow_natCast ‖(1 : ℂ) - z‖ k]
      rw [hg, hr2, norm_mul, norm_neg, norm_inv, norm_pow]
      field_simp
    have hbdd : Tendsto (fun z : ℂ => ‖(1 / 2 : ℂ) * z + (1 / 4 : ℂ) * z ^ 2‖)
        (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 ‖(1 / 2 : ℂ) * 1 + (1 / 4 : ℂ) * 1 ^ 2‖) := by
      apply Tendsto.mono_left _ nhdsWithin_le_nhds
      exact (Continuous.norm (by fun_prop)).tendsto 1
    have hloginv : Tendsto (fun z : ℂ => (Real.log (‖(1 : ℂ) - z‖⁻¹))⁻¹)
        (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0) := by
      have hnorm0 : Tendsto (fun z : ℂ => ‖(1 : ℂ) - z‖) (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0) := by
        apply Tendsto.mono_left _ nhdsWithin_le_nhds
        have : Continuous (fun z : ℂ => ‖(1 : ℂ) - z‖) := by fun_prop
        have h := this.tendsto 1
        simpa using h
      have hinvAtTop : Tendsto (fun z : ℂ => ‖(1 : ℂ) - z‖⁻¹)
          (𝓝[DeltaDomainArg R φ] (1 : ℂ)) atTop := by
        apply Filter.Tendsto.comp tendsto_inv_nhdsGT_zero
        rw [tendsto_nhdsWithin_iff]
        refine ⟨hnorm0, ?_⟩
        filter_upwards [self_mem_nhdsWithin] with z hz
        exact norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hz.2.1))
      exact tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp hinvAtTop)
    have hRHS_tends : Tendsto (fun z : ℂ =>
        ‖(1 / 2 : ℂ) * z + (1 / 4 : ℂ) * z ^ 2‖ * (Real.log (‖(1 : ℂ) - z‖⁻¹))⁻¹)
        (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0) := by
      have := hbdd.mul hloginv
      simpa using this
    refine hRHS_tends.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (hEq z hz).symm
  have htransfer := log_transfer_theorem_natural_remainder_unconditional
    (α := (k : ℝ)) (C := (1 / 2 : ℂ)) (R := R) (φ := φ)
    (f := undirectedCycleMarkedPermTupleFun k)
    (p := PowerSeries.toFMLS (PowerSeries.mapℂ (undirectedCycleMarkedPermTupleClass k).egf))
    hkR (by norm_num) (by rw [hR_def]; norm_num) hφ0 hφ2
    (undirectedCycleMarkedPermTupleFun_hasFPowerSeriesAt hk1)
    (analyticOnNhd_undirectedCycleMarkedPermTupleFun_deltaDomain hφ0 hφπ)
    hsing
  have hLHS : (fun n : ℕ =>
        (PowerSeries.toFMLS (PowerSeries.mapℂ (undirectedCycleMarkedPermTupleClass k).egf)).coeff n)
      = (fun n : ℕ =>
          ((((undirectedCycleMarkedPermTupleClass k).counts n : ℝ) / (n.factorial : ℝ)
            : ℝ) : ℂ)) := by
    funext n
    rw [PowerSeries.coeff_toFMLS, PowerSeries.coeff_mapℂ, CombClass.coeff_egf]
    push_cast; ring
  have hRHS : (fun n : ℕ => (1 / 2 : ℂ) *
        (((n : ℝ) ^ ((k : ℝ) - 1) / Real.Gamma (k : ℝ) * Real.log n : ℝ) : ℂ))
      = (fun n : ℕ => (((1 / 2 : ℝ) * ((n : ℝ) ^ (k - 1) / ((k - 1).factorial : ℝ))
          * Real.log n : ℝ) : ℂ)) := by
    funext n
    have hΓ : Real.Gamma (k : ℝ) = ((k - 1).factorial : ℝ) := by
      have hkk : (k : ℝ) = ((k - 1 : ℕ) : ℝ) + 1 := by
        have : k - 1 + 1 = k := by omega
        rw [← this]; push_cast; ring
      rw [hkk, Real.Gamma_nat_eq_factorial]
    have hpow : ((n : ℝ) ^ ((k : ℝ) - 1)) = (n : ℝ) ^ (k - 1) := by
      have hkk : ((k : ℝ) - 1) = (((k - 1 : ℕ)) : ℝ) := by
        have : k - 1 + 1 = k := by omega
        rw [← this]; push_cast; ring
      rw [hkk, Real.rpow_natCast]
    rw [hΓ, hpow]
    push_cast; ring
  rw [hLHS, hRHS] at htransfer
  exact ofReal_isEquivalent_iff.mp htransfer

end AnalyticCombinatorics
