import AnalyticCombinatorics.Ch4.Analytic.LogSqCoeff
import AnalyticCombinatorics.Ch4.Analytic.LogSqSingularity
import AnalyticCombinatorics.Ch4.Analytic.LogFaithful
import AnalyticCombinatorics.Ch4.Analytic.LogTransferBranch
import AnalyticCombinatorics.Ch4.Analytic.LittleOTransfer

/-!
# Squared-logarithm singularity transfer (strong-remainder form)

`(1-z)^{-α}·log²(1/(1-z))` with strong residual `o(|1-z|^{-α})` ⟹
`[zⁿ]f ~ C·n^{α-1}/Γ(α)·(log n)²`.

The model coefficient identity is `coeff_logSqGF_eq_logSqSingularityCoeffℂ` (LogSqCoeff) and the
real asymptotic is `logSqSingularityScale_isEquivalent` (LogSqSingularity).  As in the one-log
strong-remainder transfer, the residual error `o(n^{α-1})` from the algebraic Darboux descent is
absorbed into `o(n^{α-1}(log n)²)` — no new contour estimate.
-/

open Complex Filter Asymptotics
open scoped Topology BigOperators

/-- The squared-logarithm model function. -/
noncomputable def logSqSingularityFun (α : ℂ) : ℂ → ℂ :=
  fun z => (1 - z) ^ (-α) * (-Complex.log (1 - z)) ^ 2

/-- `n^{α-1}` is negligible against `n^{α-1} (log n)²`. -/
lemma algebraic_scale_isLittleO_log_sq_scale {α : ℝ} :
    (fun n : ℕ => (n : ℝ) ^ (α - 1))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 1) * (Real.log n) ^ 2) := by
  have hlog_atTop : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsq_atTop : Tendsto (fun n : ℕ => (Real.log n) ^ 2) atTop atTop := by
    have := hlog_atTop.atTop_mul_atTop₀ hlog_atTop
    refine this.congr (fun n => ?_); rw [pow_two]
  have hlog : (fun _ : ℕ => (1 : ℝ)) =o[atTop] (fun n : ℕ => (Real.log n) ^ 2) :=
    (isLittleO_one_left_iff ℝ).mpr (tendsto_norm_atTop_atTop.comp hsq_atTop)
  have h := (Asymptotics.isBigO_refl (fun n : ℕ => (n : ℝ) ^ (α - 1)) atTop).mul_isLittleO hlog
  simpa using h

namespace AnalyticCombinatorics

/-- Norm-summability of the `logSingularityGF` coefficient series on the unit ball. -/
lemma logSingularityGF_summable_norm {α z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ => ‖PowerSeries.coeff (R := ℂ) n (logSingularityGF α) * z ^ n‖) := by
  have hf := oneSubCpowGF_summable_norm (α := α) (z := z) hz
  have hg := logGF_summable_norm (z := z) hz
  have hfn : Summable (fun j : ℕ => ‖‖PowerSeries.coeff (R := ℂ) j (oneSubCpowGF α) * z ^ j‖‖) := by
    simpa using hf
  have hgn : Summable (fun k : ℕ => ‖‖PowerSeries.coeff (R := ℂ) k logGF * z ^ k‖‖) := by
    simpa using hg
  have hbig := summable_sum_mul_antidiagonal_of_summable_norm' hfn hf hgn hg
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hbig
  rw [logSingularityGF, PowerSeries.coeff_mul, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p hp => ?_)
  rw [Finset.mem_antidiagonal] at hp
  have heq : PowerSeries.coeff (R := ℂ) p.1 (oneSubCpowGF α) *
        PowerSeries.coeff (R := ℂ) p.2 logGF * z ^ n
      = (PowerSeries.coeff (R := ℂ) p.1 (oneSubCpowGF α) * z ^ p.1) *
        (PowerSeries.coeff (R := ℂ) p.2 logGF * z ^ p.2) := by
    rw [← hp, pow_add]; ring
  rw [heq, norm_mul]

/-- **Faithfulness**: `logSqSingularityFun α` has power series `logSqGF α` at `0`. -/
theorem logSqSingularityFun_hasFPowerSeriesAt (α : ℂ) :
    HasFPowerSeriesAt (logSqSingularityFun α) (PowerSeries.toFMLS (logSqGF α)) 0 := by
  rw [hasFPowerSeriesAt_iff]
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with z hz
  have hz_norm : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hz
  have hlog1 := hasSum_powerSeries_mul (oneSubCpowGF α) logGF
    (oneSubCpowGF_hasSum (α := α) hz_norm) (logGF_hasSum hz_norm)
    (oneSubCpowGF_summable_norm (α := α) hz_norm) (logGF_summable_norm hz_norm)
  rw [← logSingularityGF] at hlog1
  have hprod := hasSum_powerSeries_mul (logSingularityGF α) logGF
    hlog1 (logGF_hasSum hz_norm) (logSingularityGF_summable_norm hz_norm)
    (logGF_summable_norm hz_norm)
  have hval : (1 - z) ^ (-α) * (-Complex.log (1 - z)) * (-Complex.log (1 - z))
      = logSqSingularityFun α z := by rw [logSqSingularityFun, sq]; ring
  rw [← logSqGF, hval] at hprod
  simpa [PowerSeries.coeff_toFMLS, smul_eq_mul, mul_comm] using hprod

/-- **Δ-analyticity** of the squared-log model. -/
theorem analyticOnNhd_logSqSingularityFun_deltaDomain {α : ℂ} {R φ : ℝ}
    (hφ0 : 0 < φ) (hφπ : φ < Real.pi) :
    AnalyticOnNhd ℂ (logSqSingularityFun α) (DeltaDomainArg R φ) := by
  have hpow : AnalyticOnNhd ℂ (fun z : ℂ => (1 - z) ^ (-α)) (DeltaDomainArg R φ) :=
    analyticOnNhd_one_sub_cpow_deltaDomain (α := α) hφ0 hφπ
  have hlog : AnalyticOnNhd ℂ (fun z : ℂ => -Complex.log (1 - z)) (DeltaDomainArg R φ) :=
    analyticOnNhd_negLog_one_sub_deltaDomain (R := R) (φ := φ) hφ0
  have hfun : logSqSingularityFun α
      = fun z : ℂ => (1 - z) ^ (-α) * ((-Complex.log (1 - z)) * (-Complex.log (1 - z))) := by
    funext z; rw [logSqSingularityFun, sq]
  rw [hfun]
  exact hpow.mul (hlog.mul hlog)

/-- Real/complex bridge: `(logSqSingularityScale α n : ℂ) = logSqSingularityCoeffℂ (↑α) n`. -/
theorem logSqSingularityScale_cast (α : ℝ) (n : ℕ) :
    (logSqSingularityScale α n : ℂ) = logSqSingularityCoeffℂ (α : ℂ) n := by
  have hchoose : Ring.choose (((α : ℂ) + n - 1)) n = ((Ring.choose (α + n - 1) n : ℝ) : ℂ) := by
    rw [Ring.choose, Ring.choose]
    change Ring.multichoose ((α : ℂ) + n - 1 - n + 1) n =
      (algebraMap ℝ ℂ) (Ring.multichoose ((α + n - 1 : ℝ) - n + 1) n)
    rw [Ring.map_multichoose (algebraMap ℝ ℂ) ((α + n - 1 : ℝ) - n + 1) n]
    congr 1
    norm_num [Complex.ofReal_add, Complex.ofReal_sub]
  have hharm : ((shiftedHarmonic α n : ℝ) : ℂ) = shiftedHarmonicℂ (α : ℂ) n := by
    rw [shiftedHarmonic, shiftedHarmonicℂ, Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Complex.ofReal_inv, Complex.ofReal_add, Complex.ofReal_natCast]
  have hharm2 : ((shiftedHarmonic2 α n : ℝ) : ℂ) = shiftedHarmonic2ℂ (α : ℂ) n := by
    rw [shiftedHarmonic2, shiftedHarmonic2ℂ, Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Complex.ofReal_inv, Complex.ofReal_pow, Complex.ofReal_add, Complex.ofReal_natCast,
      ← inv_pow]
  rw [logSqSingularityScale, logSqSingularityCoeffℂ, binCoeffℂ, Complex.ofReal_mul, ← hchoose,
    Complex.ofReal_sub, Complex.ofReal_pow, hharm, hharm2]

theorem logSqSingularityScale_eq_coeff_logSqGF {α : ℝ} (hα : ∀ m : ℕ, (α : ℂ) ≠ -m) (n : ℕ) :
    (logSqSingularityScale α n : ℂ) = PowerSeries.coeff (R := ℂ) n (logSqGF (α : ℂ)) := by
  rw [logSqSingularityScale_cast, coeff_logSqGF_eq_logSqSingularityCoeffℂ (α : ℂ) hα n]

/-- **Strong-remainder squared-logarithm transfer.**  `α > 1`, residual `o(|1-z|^{-α})` ⟹
`[zⁿ]f ~ C·n^{α-1}/Γ(α)·(log n)²`. -/
theorem logSq_transfer_theorem_strong_remainder
    {α : ℝ} {C : ℂ} {R φ : ℝ} {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hα : 1 < α) (hC : C ≠ 0) (hR : 1 < R) (hφ0 : 0 < φ) (hφ2 : φ < Real.pi / 2)
    (hp : HasFPowerSeriesAt f p 0)
    (hΔ : AnalyticOnNhd ℂ f (DeltaDomainArg R φ))
    (hsing : Tendsto
      (fun z : ℂ => ‖f z - C * logSqSingularityFun (α : ℂ) z‖ * ‖(1 : ℂ) - z‖ ^ α)
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0)) :
    (fun n : ℕ => p.coeff n) ~[atTop]
      (fun n : ℕ => C * (((n : ℝ) ^ (α - 1) / Real.Gamma α * (Real.log n) ^ 2 : ℝ) : ℂ)) := by
  classical
  set q : FormalMultilinearSeries ℂ ℂ ℂ := PowerSeries.toFMLS (logSqGF (α : ℂ)) with hq
  have hαneg : ∀ m : ℕ, (α : ℂ) ≠ -m := by
    intro m hm
    have hre := congrArg Complex.re hm
    simp only [Complex.ofReal_re, Complex.neg_re, Complex.natCast_re] at hre
    have : (0 : ℝ) ≤ (m : ℝ) := by positivity
    linarith
  have hqcoeff : ∀ n, q.coeff n = (logSqSingularityScale α n : ℂ) := by
    intro n
    rw [hq, PowerSeries.coeff_toFMLS, ← logSqSingularityScale_eq_coeff_logSqGF hαneg]
  have hmain : (fun n : ℕ => C * q.coeff n)
      ~[atTop] (fun n : ℕ => C * (((n : ℝ) ^ (α - 1) / Real.Gamma α * (Real.log n) ^ 2 : ℝ) : ℂ)) := by
    have hcomplex : (fun n : ℕ => (logSqSingularityScale α n : ℂ))
        ~[atTop] (fun n : ℕ => (((n : ℝ) ^ (α - 1) / Real.Gamma α * (Real.log n) ^ 2 : ℝ) : ℂ)) := by
      rw [ofReal_isEquivalent_iff]
      simpa [mul_assoc] using logSqSingularityScale_isEquivalent hα
    have hmul := (Asymptotics.IsEquivalent.refl (u := fun _ : ℕ => C)).mul hcomplex
    simp only [hqcoeff]; exact hmul
  have hpg : HasFPowerSeriesAt (fun z : ℂ => f z - C • logSqSingularityFun (α : ℂ) z) (p - C • q) 0 :=
    hp.sub ((logSqSingularityFun_hasFPowerSeriesAt (α : ℂ)).const_smul (c := C))
  have hΔg : AnalyticOnNhd ℂ (fun z : ℂ => f z - C • logSqSingularityFun (α : ℂ) z)
      (DeltaDomainArg R φ) :=
    hΔ.sub ((analyticOnNhd_logSqSingularityFun_deltaDomain hφ0
      (by linarith [Real.pi_pos] : φ < Real.pi)).const_smul (c := C))
  have herr_norm : (fun n : ℕ => ‖(p - C • q).coeff n‖)
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 1)) := by
    refine coeff_norm_isLittleO_atTop_of_delta_littleO_beta_gt_one
      (R := R) (φ := φ) (β := α)
      (f := fun z : ℂ => f z - C • logSqSingularityFun (α : ℂ) z) (p := p - C • q)
      hR hφ0 hφ2 hpg hΔg ?_ hα
    simpa [smul_eq_mul] using hsing
  have hΓ : 0 < Real.Gamma α := Real.Gamma_pos_of_pos (by linarith)
  have hCnorm : 0 < ‖C‖ := norm_pos_iff.mpr hC
  have hscale_bigO : (fun n : ℕ => (n : ℝ) ^ (α - 1))
      =O[atTop] (fun n : ℕ => C * (((n : ℝ) ^ (α - 1) / Real.Gamma α * (Real.log n) ^ 2 : ℝ) : ℂ)) := by
    have habs : (fun n : ℕ => (n : ℝ) ^ (α - 1))
        =o[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 1) * (Real.log n) ^ 2) :=
      algebraic_scale_isLittleO_log_sq_scale
    have hpos : (fun n : ℕ => (n : ℝ) ^ (α - 1) * (Real.log n) ^ 2)
        =O[atTop] (fun n : ℕ => C * (((n : ℝ) ^ (α - 1) / Real.Gamma α * (Real.log n) ^ 2 : ℝ) : ℂ)) := by
      rw [Asymptotics.isBigO_iff]
      refine ⟨Real.Gamma α / ‖C‖, ?_⟩
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn1
      have hpow : 0 ≤ (n : ℝ) ^ (α - 1) := (Real.rpow_pos_of_pos (by linarith) _).le
      rw [Real.norm_of_nonneg (by positivity), norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
      apply le_of_eq
      field_simp
    exact (habs.trans_isBigO hpos).isBigO
  have herr_target : (fun n : ℕ => (p - C • q).coeff n)
      =o[atTop] (fun n : ℕ => C * (((n : ℝ) ^ (α - 1) / Real.Gamma α * (Real.log n) ^ 2 : ℝ) : ℂ)) :=
    (Asymptotics.IsLittleO.of_norm_left herr_norm).trans_isBigO hscale_bigO
  have hsum : (fun n : ℕ => C * q.coeff n + (p - C • q).coeff n)
      ~[atTop] (fun n : ℕ => C * (((n : ℝ) ^ (α - 1) / Real.Gamma α * (Real.log n) ^ 2 : ℝ) : ℂ)) :=
    hmain.add_isLittleO herr_target
  have hdecomp : (fun n : ℕ => p.coeff n)
      =ᶠ[atTop] (fun n : ℕ => C * q.coeff n + (p - C • q).coeff n) := by
    refine Eventually.of_forall fun n => ?_
    show p.coeff n = C * q.coeff n + (p - C • q).coeff n
    have hcs : (p - C • q).coeff n = p.coeff n - C * q.coeff n := by
      change (p n - (C • q) n) 1 = p n 1 - C * q.coeff n
      rw [FormalMultilinearSeries.smul_apply, ContinuousMultilinearMap.sub_apply,
        ContinuousMultilinearMap.smul_apply]
      change p.coeff n - C • q.coeff n = p.coeff n - C * q.coeff n
      simp [smul_eq_mul]
    rw [hcs]; ring
  exact hdecomp.trans_isEquivalent hsum

/-- **Unconditional** strong-remainder squared-logarithm transfer. -/
theorem logSq_transfer_theorem_strong_remainder_unconditional
    {α : ℝ} {C : ℂ} {R φ : ℝ} {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hα : 1 < α) (hC : C ≠ 0) (hR : 1 < R) (hφ0 : 0 < φ) (hφ2 : φ < Real.pi / 2)
    (hp : HasFPowerSeriesAt f p 0)
    (hΔ : AnalyticOnNhd ℂ f (DeltaDomainArg R φ))
    (hsing : Tendsto
      (fun z : ℂ => ‖f z - C * logSqSingularityFun (α : ℂ) z‖ * ‖(1 : ℂ) - z‖ ^ α)
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0)) :
    (fun n : ℕ => p.coeff n) ~[atTop]
      (fun n : ℕ => C * (((n : ℝ) ^ (α - 1) / Real.Gamma α * (Real.log n) ^ 2 : ℝ) : ℂ)) :=
  logSq_transfer_theorem_strong_remainder hα hC hR hφ0 hφ2 hp hΔ hsing

end AnalyticCombinatorics
