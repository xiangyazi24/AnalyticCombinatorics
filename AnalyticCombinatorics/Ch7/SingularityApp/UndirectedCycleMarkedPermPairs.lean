import AnalyticCombinatorics.Ch7.SingularityApp.CycleMarkedPermPairs
import AnalyticCombinatorics.Ch7.SingularityApp.TwoRegularClass
import AnalyticCombinatorics.Ch4.Analytic.LogTransferNatural

/-!
# A labelled class that genuinely needs the natural-remainder log transfer

`cycleMarkedPermPairClass` (CycleMarkedPermPairs.lean) had EGF *exactly*
`(1-z)^{-2}(-log(1-z))` — zero singular remainder — so it did not distinguish the
natural-remainder transfer from the strong one.  This file gives the first class that
**only** the natural-remainder transfer can handle:

  `A := (undirectedCycleClass ⋆ permutations) ⋆ permutations`

— an ordered pair of permutations carrying one distinguished *undirected* cycle of length
≥ 3 — with EGF

  `A(z) = (½·log(1/(1-z)) - z/2 - z²/4)·(1-z)^{-2}`
        `= ½·(1-z)^{-2}(-log(1-z))  -  (z/2 + z²/4)(1-z)^{-2}`.

The residual `-(z/2+z²/4)(1-z)^{-2}` satisfies `‖residual‖·‖1-z‖² → 3/4 ≠ 0` (so it is
NOT `o(|1-z|^{-2})` — the strong-remainder transfer fails), but `‖residual‖·‖1-z‖²/log(1/‖1-z‖) → 0`
(so the natural-remainder transfer applies).  Hence

  `aₙ / n! ~ ½·n·log n`.
-/

open Complex Filter Asymptotics
open scoped BigOperators PowerSeries Topology

noncomputable section

namespace AnalyticCombinatorics

open AnalyticCombinatorics.Ch1
open AnalyticCombinatorics.Ch5.Meromorphic.Alignments

/-- A permutation pair with a distinguished undirected cycle (length ≥ 3) in the first factor. -/
def undirectedCycleMarkedPermPairClass : CombClass :=
  (TwoRegularClass.undirectedCycleClass.lprod CombClass.permutations).lprod CombClass.permutations

/-! ### Formal EGF identity `mapℂ A.egf = twoRegularCoreEGFℂ · oneSubCpowGF 2` -/

theorem mapℂ_undirectedCycleMarkedPermPairClass_egf :
    PowerSeries.mapℂ undirectedCycleMarkedPermPairClass.egf
      = TwoRegularClass.twoRegularCoreEGFℂ * oneSubCpowGF 2 := by
  rw [undirectedCycleMarkedPermPairClass, CombClass.egf_lprod, CombClass.egf_lprod,
    map_mul, map_mul, mul_assoc, mapℂ_perm_sq_eq_oneSubCpowGF_two,
    TwoRegularClass.twoRegularCoreEGFℂ]

/-! ### Per-`z` realization of `twoRegularCoreEGFℂ` (for the Cauchy product) -/

/-- `twoRegularCoreEGFℂ` realizes `twoRegularCoreFun` on the unit ball. -/
lemma twoRegularCore_hasSum {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => PowerSeries.coeff (R := ℂ) n TwoRegularClass.twoRegularCoreEGFℂ * z ^ n)
      (TwoRegularClass.twoRegularCoreFun z) := by
  have hcyc : HasSum
      (fun n : ℕ => PowerSeries.coeff (R := ℂ) n cycleEGFℂ * z ^ n) (-Complex.log (1 - z)) := by
    rw [show cycleEGFℂ = logGF from (logGF_eq_cycleEGFℂ).symm]; exact logGF_hasSum hz
  have hX : HasSum
      (fun n : ℕ => PowerSeries.coeff (R := ℂ) n (PowerSeries.X : PowerSeries ℂ) * z ^ n) z := by
    have h := hasSum_single (b := 1)
      (f := fun n : ℕ => PowerSeries.coeff (R := ℂ) n (PowerSeries.X : PowerSeries ℂ) * z ^ n)
      (fun n hn => by simp [PowerSeries.coeff_X, hn])
    simpa [PowerSeries.coeff_X] using h
  have hX2 : HasSum
      (fun n : ℕ => PowerSeries.coeff (R := ℂ) n ((PowerSeries.X : PowerSeries ℂ) ^ 2) * z ^ n)
      (z ^ 2) := by
    have h := hasSum_single (b := 2)
      (f := fun n : ℕ => PowerSeries.coeff (R := ℂ) n ((PowerSeries.X : PowerSeries ℂ) ^ 2) * z ^ n)
      (fun n hn => by simp [PowerSeries.coeff_X_pow, hn])
    simpa [PowerSeries.coeff_X_pow] using h
  have hval : (2⁻¹ : ℂ) * (-Complex.log (1 - z)) - 2⁻¹ * z - 4⁻¹ * z ^ 2
      = TwoRegularClass.twoRegularCoreFun z := by
    simp only [TwoRegularClass.twoRegularCoreFun, cycleAnalyticFun, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
  have hfun : (fun n : ℕ => PowerSeries.coeff (R := ℂ) n TwoRegularClass.twoRegularCoreEGFℂ * z ^ n)
      = (fun n : ℕ => (2⁻¹ : ℂ) * (PowerSeries.coeff (R := ℂ) n cycleEGFℂ * z ^ n)
          - (2⁻¹ : ℂ) * (PowerSeries.coeff (R := ℂ) n (PowerSeries.X : PowerSeries ℂ) * z ^ n)
          - (4⁻¹ : ℂ) * (PowerSeries.coeff (R := ℂ) n ((PowerSeries.X : PowerSeries ℂ) ^ 2)
              * z ^ n)) := by
    funext n
    rw [TwoRegularClass.twoRegularCoreEGFℂ_eq, TwoRegularClass.twoRegularCoreSeriesℂ]
    simp only [map_sub, map_smul, smul_eq_mul]
    ring
  rw [hfun, ← hval]
  exact ((hcyc.mul_left (2⁻¹ : ℂ)).sub (hX.mul_left (2⁻¹ : ℂ))).sub (hX2.mul_left (4⁻¹ : ℂ))

/-- `twoRegularCoreEGFℂ` factor series is norm-summable on the unit ball. -/
lemma twoRegularCore_summable_norm {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ =>
      ‖PowerSeries.coeff (R := ℂ) n TwoRegularClass.twoRegularCoreEGFℂ * z ^ n‖) := by
  have hgeo := summable_geometric_of_lt_one (norm_nonneg z) hz
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) (hgeo.mul_left (5 / 4))
  rw [norm_mul, norm_pow]
  have hnorm_half : ‖(2⁻¹ : ℂ)‖ = 2⁻¹ := by rw [norm_inv]; norm_num [Complex.norm_ofNat]
  have hnorm_quart : ‖(4⁻¹ : ℂ)‖ = 4⁻¹ := by rw [norm_inv]; norm_num [Complex.norm_ofNat]
  have hcoeff : ‖PowerSeries.coeff (R := ℂ) n TwoRegularClass.twoRegularCoreEGFℂ‖ ≤ 5 / 4 := by
    rw [TwoRegularClass.twoRegularCoreEGFℂ_eq, TwoRegularClass.twoRegularCoreSeriesℂ]
    simp only [map_sub, map_smul, smul_eq_mul, coeff_cycleEGFℂ]
    have ha : ‖(2⁻¹ : ℂ) * (n : ℂ)⁻¹‖ ≤ 2⁻¹ := by
      rw [norm_mul, hnorm_half]
      have hn1 : ‖((n : ℂ))⁻¹‖ ≤ 1 := by
        rcases Nat.eq_zero_or_pos n with hn | hn
        · simp [hn]
        · rw [norm_inv, Complex.norm_natCast, inv_le_one_iff₀]; right; exact_mod_cast hn
      nlinarith [hn1, norm_nonneg ((n : ℂ)⁻¹)]
    have hb : ‖(2⁻¹ : ℂ) * PowerSeries.coeff (R := ℂ) n (PowerSeries.X : PowerSeries ℂ)‖ ≤ 2⁻¹ := by
      rw [norm_mul, hnorm_half]
      have : ‖PowerSeries.coeff (R := ℂ) n (PowerSeries.X : PowerSeries ℂ)‖ ≤ 1 := by
        rw [PowerSeries.coeff_X]; split <;> simp
      nlinarith [this, norm_nonneg (PowerSeries.coeff (R := ℂ) n (PowerSeries.X : PowerSeries ℂ))]
    have hc : ‖(4⁻¹ : ℂ) * PowerSeries.coeff (R := ℂ) n ((PowerSeries.X : PowerSeries ℂ) ^ 2)‖
        ≤ 4⁻¹ := by
      rw [norm_mul, hnorm_quart]
      have : ‖PowerSeries.coeff (R := ℂ) n ((PowerSeries.X : PowerSeries ℂ) ^ 2)‖ ≤ 1 := by
        rw [PowerSeries.coeff_X_pow]; split <;> simp
      nlinarith [this,
        norm_nonneg (PowerSeries.coeff (R := ℂ) n ((PowerSeries.X : PowerSeries ℂ) ^ 2))]
    have htri : ‖(2⁻¹ : ℂ) * (n : ℂ)⁻¹ - 2⁻¹ * PowerSeries.coeff (R := ℂ) n PowerSeries.X
          - 4⁻¹ * PowerSeries.coeff (R := ℂ) n (PowerSeries.X ^ 2)‖
        ≤ ‖(2⁻¹ : ℂ) * (n : ℂ)⁻¹‖
          + ‖(2⁻¹ : ℂ) * PowerSeries.coeff (R := ℂ) n PowerSeries.X‖
          + ‖(4⁻¹ : ℂ) * PowerSeries.coeff (R := ℂ) n (PowerSeries.X ^ 2)‖ := by
      have h1 := norm_sub_le ((2⁻¹ : ℂ) * (n : ℂ)⁻¹
        - 2⁻¹ * PowerSeries.coeff (R := ℂ) n PowerSeries.X)
        ((4⁻¹ : ℂ) * PowerSeries.coeff (R := ℂ) n (PowerSeries.X ^ 2))
      have h2 := norm_sub_le ((2⁻¹ : ℂ) * (n : ℂ)⁻¹)
        ((2⁻¹ : ℂ) * PowerSeries.coeff (R := ℂ) n PowerSeries.X)
      linarith
    linarith [htri, ha, hb, hc]
  calc ‖PowerSeries.coeff (R := ℂ) n TwoRegularClass.twoRegularCoreEGFℂ‖ * ‖z‖ ^ n
      ≤ (5 / 4) * ‖z‖ ^ n := mul_le_mul_of_nonneg_right hcoeff (by positivity)

/-! ### The analytic carrier and its power series -/

/-- Analytic representative: `twoRegularCoreFun(z)·(1-z)^{-2}`. -/
def undirectedCycleMarkedPermPairFun (z : ℂ) : ℂ :=
  TwoRegularClass.twoRegularCoreFun z * (1 - z) ^ (-(2 : ℂ))

lemma undirectedCycleMarkedPermPairFun_hasFPowerSeriesAt :
    HasFPowerSeriesAt undirectedCycleMarkedPermPairFun
      (PowerSeries.toFMLS (PowerSeries.mapℂ undirectedCycleMarkedPermPairClass.egf)) 0 := by
  rw [hasFPowerSeriesAt_iff]
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with z hz
  have hz_norm : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hz
  have hprod := hasSum_powerSeries_mul TwoRegularClass.twoRegularCoreEGFℂ (oneSubCpowGF 2)
    (twoRegularCore_hasSum hz_norm)
    (oneSubCpowGF_hasSum (α := 2) (z := z) hz_norm)
    (twoRegularCore_summable_norm hz_norm)
    (oneSubCpowGF_summable_norm (α := 2) (z := z) hz_norm)
  rw [mapℂ_undirectedCycleMarkedPermPairClass_egf]
  simpa [undirectedCycleMarkedPermPairFun, PowerSeries.coeff_toFMLS, smul_eq_mul, mul_comm]
    using hprod

/-! ### Δ-analyticity -/

lemma analyticOnNhd_undirectedCycleMarkedPermPairFun_deltaDomain {R φ : ℝ}
    (hφ0 : 0 < φ) (hφπ : φ < Real.pi) :
    AnalyticOnNhd ℂ undirectedCycleMarkedPermPairFun (DeltaDomainArg R φ) := by
  have hcpow : AnalyticOnNhd ℂ (fun z : ℂ => (1 - z) ^ (-(2 : ℂ))) (DeltaDomainArg R φ) :=
    analyticOnNhd_one_sub_cpow_deltaDomain (α := (2 : ℂ)) hφ0 hφπ
  have hfeq : undirectedCycleMarkedPermPairFun
      = fun z : ℂ => (1 / 2 : ℂ) * logSingularityFun ((2 : ℝ) : ℂ) z
          - ((1 / 2 : ℂ) * z + (1 / 4 : ℂ) * z ^ 2) * (1 - z) ^ (-(2 : ℂ)) := by
    funext z
    simp only [undirectedCycleMarkedPermPairFun, TwoRegularClass.twoRegularCoreFun,
      cycleAnalyticFun, logSingularityFun, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [show (((2 : ℝ) : ℂ)) = (2 : ℂ) by norm_num]
    ring
  rw [hfeq]
  have hlog : AnalyticOnNhd ℂ (logSingularityFun ((2 : ℝ) : ℂ)) (DeltaDomainArg R φ) :=
    analyticOnNhd_logSingularityFun_deltaDomain hφ0 hφπ
  have hpoly : AnalyticOnNhd ℂ (fun z : ℂ => (1 / 2 : ℂ) * z + (1 / 4 : ℂ) * z ^ 2)
      (DeltaDomainArg R φ) :=
    (analyticOnNhd_const.mul analyticOnNhd_id).add
      (analyticOnNhd_const.mul (analyticOnNhd_id.pow 2))
  exact (analyticOnNhd_const.mul hlog).sub (hpoly.mul hcpow)

/-! ### The natural-remainder asymptotic -/

/-- **First application requiring the natural-remainder transfer**: the residual has
`‖·‖·‖1-z‖² → 3/4 ≠ 0` (strong transfer fails) but `/log(1/‖1-z‖) → 0`.  Hence
`aₙ/n! ~ ½·n·log n`. -/
theorem undirectedCycleMarkedPermPairClass_counts_div_factorial_isEquivalent :
    (fun n : ℕ => (undirectedCycleMarkedPermPairClass.counts n : ℝ) / (n.factorial : ℝ)) ~[atTop]
      (fun n : ℕ => (1 / 2 : ℝ) * (n : ℝ) * Real.log n) := by
  set R : ℝ := 2 with hR_def
  set φ : ℝ := Real.pi / 4 with hφ_def
  have hφ0 : 0 < φ := by rw [hφ_def]; positivity
  have hφ2 : φ < Real.pi / 2 := by rw [hφ_def]; linarith [Real.pi_pos]
  have hφπ : φ < Real.pi := by linarith [Real.pi_pos]
  -- residual g = f - ½·model = -(½z+¼z²)(1-z)^{-2}
  have hsing : Tendsto
      (fun z : ℂ => ‖undirectedCycleMarkedPermPairFun z
          - (1 / 2 : ℂ) * logSingularityFun ((2 : ℝ) : ℂ) z‖
        * ‖(1 : ℂ) - z‖ ^ (2 : ℝ) * (Real.log (‖(1 : ℂ) - z‖⁻¹))⁻¹)
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0) := by
    -- on the punctured nbhd, the displayed function equals ‖½z+¼z²‖ · (log ‖1-z‖⁻¹)⁻¹
    have hEq : ∀ z ∈ DeltaDomainArg R φ,
        ‖undirectedCycleMarkedPermPairFun z - (1 / 2 : ℂ) * logSingularityFun ((2 : ℝ) : ℂ) z‖
            * ‖(1 : ℂ) - z‖ ^ (2 : ℝ) * (Real.log (‖(1 : ℂ) - z‖⁻¹))⁻¹
          = ‖(1 / 2 : ℂ) * z + (1 / 4 : ℂ) * z ^ 2‖ * (Real.log (‖(1 : ℂ) - z‖⁻¹))⁻¹ := by
      intro z hz
      have hz1 : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz.2.1)
      have hnz : ‖(1 : ℂ) - z‖ ≠ 0 := by rwa [norm_ne_zero_iff]
      have hg : undirectedCycleMarkedPermPairFun z
          - (1 / 2 : ℂ) * logSingularityFun ((2 : ℝ) : ℂ) z
          = -((1 / 2 : ℂ) * z + (1 / 4 : ℂ) * z ^ 2) * ((1 - z) ^ 2)⁻¹ := by
        simp only [undirectedCycleMarkedPermPairFun, TwoRegularClass.twoRegularCoreFun,
          cycleAnalyticFun, logSingularityFun, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        rw [show (((2 : ℝ) : ℂ)) = (2 : ℂ) by norm_num,
          show (-(2 : ℂ)) = ((-2 : ℤ) : ℂ) by norm_num, Complex.cpow_intCast]
        field_simp
        ring
      have hr2 : ‖(1 : ℂ) - z‖ ^ (2 : ℝ) = ‖(1 : ℂ) - z‖ ^ 2 := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rw [hg, hr2, norm_mul, norm_neg, norm_inv, norm_pow]
      field_simp
    -- ‖½z+¼z²‖·(log‖1-z‖⁻¹)⁻¹ → ¾·0 = 0
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
  -- apply the unconditional natural-remainder transfer at α=2, C=1/2
  have htransfer := log_transfer_theorem_natural_remainder_unconditional
    (α := (2 : ℝ)) (C := (1 / 2 : ℂ)) (R := R) (φ := φ)
    (f := undirectedCycleMarkedPermPairFun)
    (p := PowerSeries.toFMLS (PowerSeries.mapℂ undirectedCycleMarkedPermPairClass.egf))
    (by norm_num) (by norm_num) (by rw [hR_def]; norm_num) hφ0 hφ2
    undirectedCycleMarkedPermPairFun_hasFPowerSeriesAt
    (analyticOnNhd_undirectedCycleMarkedPermPairFun_deltaDomain hφ0 hφπ)
    hsing
  have hLHS : (fun n : ℕ =>
        (PowerSeries.toFMLS (PowerSeries.mapℂ undirectedCycleMarkedPermPairClass.egf)).coeff n)
      = (fun n : ℕ =>
        (((undirectedCycleMarkedPermPairClass.counts n : ℝ) / (n.factorial : ℝ) : ℝ) : ℂ)) := by
    funext n
    rw [PowerSeries.coeff_toFMLS, PowerSeries.coeff_mapℂ, CombClass.coeff_egf]
    push_cast; ring
  have hRHS : (fun n : ℕ => (1 / 2 : ℂ) *
        (((n : ℝ) ^ ((2 : ℝ) - 1) / Real.Gamma 2 * Real.log n : ℝ) : ℂ))
      = (fun n : ℕ => (((1 / 2 : ℝ) * (n : ℝ) * Real.log n : ℝ) : ℂ)) := by
    funext n
    have hΓ : Real.Gamma (2 : ℝ) = 1 := Real.Gamma_two
    push_cast [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, hΓ]
    ring
  rw [hLHS, hRHS] at htransfer
  exact ofReal_isEquivalent_iff.mp htransfer

end AnalyticCombinatorics
