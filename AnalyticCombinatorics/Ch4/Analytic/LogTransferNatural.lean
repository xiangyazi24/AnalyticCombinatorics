import AnalyticCombinatorics.Ch4.Analytic.LogFaithful
import AnalyticCombinatorics.Ch4.Analytic.LittleOTransfer

/-!
# Flajolet–Odlyzko logarithmic transfer — natural-remainder form

`LogTransfer.lean` proves the *strong-remainder* logarithmic transfer, whose residual
hypothesis is `f − C·(1−z)^{−α}·(−log(1−z)) = o(|1−z|^{−α})` (one log factor stronger
than the textbook statement).  This file removes that caveat: the **natural** residual

  `f − C·(1−z)^{−α}·(−log(1−z)) = o(|1−z|^{−α} · log(1/|1−z|))`

(encoded via `‖·‖·‖1−z‖^α / log(1/‖1−z‖) → 0`) still yields

  `[zⁿ]f ~ C · n^{α−1}/Γ(α) · log n`.

The new analytic content is the log-weighted Hankel/Cauchy contour estimate
`coeff_norm_isLittleO_atTop_of_delta_littleO_log_beta_gt_one` (in `LittleOTransfer`),
which supplies the error term `o(n^{α−1} log n)` directly — no algebraic absorption.
-/

noncomputable section

open Complex Filter Asymptotics
open scoped Topology BigOperators

/-- **Natural-remainder logarithmic transfer theorem.**  For real `α > 1`, if `f` is
`Δ`-analytic and `f − C·(1−z)^{−α}·(−log(1−z))` is `o(|1−z|^{−α} log(1/|1−z|))` near `1`,
then `[zⁿ]f ~ C·n^{α−1}/Γ(α)·log n`.  Faithfulness (`hp_log`, `hΔ_log`) is supplied
externally; the unconditional form below discharges it. -/
theorem log_transfer_theorem_natural_remainder
    {α : ℝ} {C : ℂ} {R φ : ℝ} {f : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hα : 1 < α) (hC : C ≠ 0) (hR : 1 < R) (hφ0 : 0 < φ) (hφ2 : φ < Real.pi / 2)
    (hp : HasFPowerSeriesAt f p 0)
    (hΔ : AnalyticOnNhd ℂ f (DeltaDomainArg R φ))
    (hp_log : HasFPowerSeriesAt (logSingularityFun (α : ℂ))
      (PowerSeries.toFMLS (logSingularityGF (α : ℂ))) 0)
    (hΔ_log : AnalyticOnNhd ℂ (logSingularityFun (α : ℂ)) (DeltaDomainArg R φ))
    (hsing : Tendsto
      (fun z : ℂ => ‖f z - C * logSingularityFun (α : ℂ) z‖ * ‖(1 : ℂ) - z‖ ^ α
        * (Real.log (‖(1 : ℂ) - z‖⁻¹))⁻¹)
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0)) :
    (fun n : ℕ => p.coeff n) ~[atTop]
      (fun n : ℕ => C * (((n : ℝ) ^ (α - 1) / Real.Gamma α * Real.log n : ℝ) : ℂ)) := by
  classical
  set q : FormalMultilinearSeries ℂ ℂ ℂ := PowerSeries.toFMLS (logSingularityGF (α : ℂ)) with hq
  have hαneg : ∀ m : ℕ, (α : ℂ) ≠ -m := by
    intro m hm
    have hre := congrArg Complex.re hm
    simp only [Complex.ofReal_re, Complex.neg_re, Complex.natCast_re] at hre
    have : (0 : ℝ) ≤ (m : ℝ) := by positivity
    linarith
  have hqcoeff : ∀ n, q.coeff n = (logSingularityCoeff α n : ℂ) := by
    intro n
    rw [hq, logSingularityCoeff_eq_coeff_logSingularityGF hαneg, PowerSeries.coeff_toFMLS]
  have hmain : (fun n : ℕ => C * q.coeff n)
      ~[atTop] (fun n : ℕ => C * (((n : ℝ) ^ (α - 1) / Real.Gamma α * Real.log n : ℝ) : ℂ)) := by
    have hcomplex : (fun n : ℕ => (logSingularityCoeff α n : ℂ))
        ~[atTop] (fun n : ℕ => (((n : ℝ) ^ (α - 1) / Real.Gamma α * Real.log n : ℝ) : ℂ)) := by
      rw [ofReal_isEquivalent_iff]
      simpa [mul_assoc] using logSingularityCoeff_isEquivalent hα
    have hconst : (fun _ : ℕ => C) ~[atTop] (fun _ : ℕ => C) := Asymptotics.IsEquivalent.refl
    have hmul := hconst.mul hcomplex
    simp only [hqcoeff]
    exact hmul
  have hpg : HasFPowerSeriesAt (fun z : ℂ => f z - C • logSingularityFun (α : ℂ) z)
      (p - C • q) 0 := hp.sub (hp_log.const_smul (c := C))
  have hΔg : AnalyticOnNhd ℂ (fun z : ℂ => f z - C • logSingularityFun (α : ℂ) z)
      (DeltaDomainArg R φ) := hΔ.sub (hΔ_log.const_smul (c := C))
  have herr_norm : (fun n : ℕ => ‖(p - C • q).coeff n‖)
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 1) * Real.log n) := by
    refine coeff_norm_isLittleO_atTop_of_delta_littleO_log_beta_gt_one
      (R := R) (φ := φ) (β := α)
      (f := fun z : ℂ => f z - C • logSingularityFun (α : ℂ) z) (p := p - C • q)
      hR hφ0 hφ2 hpg hΔg ?_ hα
    simpa [smul_eq_mul] using hsing
  have hΓ : 0 < Real.Gamma α := Real.Gamma_pos_of_pos (by linarith)
  have hCnorm : 0 < ‖C‖ := norm_pos_iff.mpr hC
  have hscale_bigO : (fun n : ℕ => (n : ℝ) ^ (α - 1) * Real.log n)
      =O[atTop] (fun n : ℕ => C * (((n : ℝ) ^ (α - 1) / Real.Gamma α * Real.log n : ℝ) : ℂ)) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨Real.Gamma α / ‖C‖, ?_⟩
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn1R
    have hpow : 0 ≤ (n : ℝ) ^ (α - 1) := (Real.rpow_pos_of_pos (by linarith) _).le
    have hxnn : 0 ≤ (n : ℝ) ^ (α - 1) / Real.Gamma α * Real.log n := by positivity
    apply le_of_eq
    rw [Real.norm_of_nonneg (by positivity), norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hxnn]
    field_simp
  have herr_target : (fun n : ℕ => (p - C • q).coeff n)
      =o[atTop] (fun n : ℕ => C * (((n : ℝ) ^ (α - 1) / Real.Gamma α * Real.log n : ℝ) : ℂ)) :=
    (Asymptotics.IsLittleO.of_norm_left herr_norm).trans_isBigO hscale_bigO
  have hsum : (fun n : ℕ => C * q.coeff n + (p - C • q).coeff n)
      ~[atTop] (fun n : ℕ => C * (((n : ℝ) ^ (α - 1) / Real.Gamma α * Real.log n : ℝ) : ℂ)) :=
    hmain.add_isLittleO herr_target
  have hdecomp : (fun n : ℕ => p.coeff n)
      =ᶠ[atTop] (fun n : ℕ => C * q.coeff n + (p - C • q).coeff n) := by
    refine Eventually.of_forall fun n => ?_
    show p.coeff n = C * q.coeff n + (p - C • q).coeff n
    have hcs : (p - C • q).coeff n = p.coeff n - C * q.coeff n := by
      change (p n - (C • q) n) 1 = p n 1 - C * q.coeff n
      rw [FormalMultilinearSeries.smul_apply,
        ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.smul_apply]
      change p.coeff n - C • q.coeff n = p.coeff n - C * q.coeff n
      simp [smul_eq_mul]
    rw [hcs]; ring
  exact hdecomp.trans_isEquivalent hsum

namespace AnalyticCombinatorics

/-- **Unconditional natural-remainder logarithmic transfer.**  Discharges both
faithfulness hypotheses of `log_transfer_theorem_natural_remainder`. -/
theorem log_transfer_theorem_natural_remainder_unconditional
    {α : ℝ} {C : ℂ} {R φ : ℝ} {f : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hα : 1 < α) (hC : C ≠ 0) (hR : 1 < R) (hφ0 : 0 < φ) (hφ2 : φ < Real.pi / 2)
    (hp : HasFPowerSeriesAt f p 0)
    (hΔ : AnalyticOnNhd ℂ f (DeltaDomainArg R φ))
    (hsing : Tendsto
      (fun z : ℂ => ‖f z - C * logSingularityFun (α : ℂ) z‖ * ‖(1 : ℂ) - z‖ ^ α
        * (Real.log (‖(1 : ℂ) - z‖⁻¹))⁻¹)
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0)) :
    (fun n : ℕ => p.coeff n) ~[atTop]
      (fun n : ℕ => C * (((n : ℝ) ^ (α - 1) / Real.Gamma α * Real.log n : ℝ) : ℂ)) :=
  log_transfer_theorem_natural_remainder hα hC hR hφ0 hφ2 hp hΔ
    (logSingularityFun_hasFPowerSeriesAt (α : ℂ))
    (analyticOnNhd_logSingularityFun_deltaDomain hφ0 (by linarith [Real.pi_pos] : φ < Real.pi))
    hsing

end AnalyticCombinatorics
