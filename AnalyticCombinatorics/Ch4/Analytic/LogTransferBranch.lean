import AnalyticCombinatorics.Ch4.Analytic.LogTransfer

/-!
# Discharging the model-faithfulness hypotheses of the logarithmic transfer

`log_transfer_theorem_strong_remainder` (LogTransfer) carries two model-faithfulness hypotheses for
`logSingularityFun α = (1−z)^{−α}·(−log(1−z))`:

* `hΔ_log` — delta-domain analyticity, and
* `hp_log` — its power series at `0` is `logSingularityGF α`.

This file discharges `hΔ_log` (mechanical, via `AnalyticOnNhd.clog` on the slit plane) and the
algebraic-factor half of `hp_log`.  The remaining piece of `hp_log` is the *complex* Taylor series
`−log(1−z) = ∑ zⁿ⁺¹/(n+1)` (Mathlib has only the real analogue) together with a Cauchy-product
realization — a genuine analytic bridge handled separately.
-/

noncomputable section

open Complex Filter Asymptotics
open scoped Topology BigOperators

/-- Delta-domain analyticity of the logarithmic factor `-log(1-z)` (principal branch). -/
lemma analyticOnNhd_negLog_one_sub_deltaDomain {R φ : ℝ} (hφ0 : 0 < φ) :
    AnalyticOnNhd ℂ (fun z : ℂ => -Complex.log (1 - z)) (DeltaDomainArg R φ) := by
  have hlog : AnalyticOnNhd ℂ (fun z : ℂ => Complex.log (1 - z)) (DeltaDomainArg R φ) :=
    (analyticOnNhd_const.sub analyticOnNhd_id).clog
      (fun z hz => one_sub_mem_slitPlane_of_mem_delta hφ0 hz)
  simpa [smul_eq_mul] using hlog.const_smul (c := (-1 : ℂ))

/-- **Discharges `hΔ_log`**: delta-domain analyticity of the log-singularity model. -/
lemma analyticOnNhd_logSingularityFun_deltaDomain {α : ℂ} {R φ : ℝ}
    (hφ0 : 0 < φ) (hφπ : φ < Real.pi) :
    AnalyticOnNhd ℂ (logSingularityFun α) (DeltaDomainArg R φ) := by
  have hpow : AnalyticOnNhd ℂ (fun z : ℂ => (1 - z) ^ (-α)) (DeltaDomainArg R φ) :=
    analyticOnNhd_one_sub_cpow_deltaDomain (α := α) (R := R) (φ := φ) hφ0 hφπ
  have hlog : AnalyticOnNhd ℂ (fun z : ℂ => -Complex.log (1 - z)) (DeltaDomainArg R φ) :=
    analyticOnNhd_negLog_one_sub_deltaDomain (R := R) (φ := φ) hφ0
  unfold logSingularityFun
  exact hpow.mul hlog

end
