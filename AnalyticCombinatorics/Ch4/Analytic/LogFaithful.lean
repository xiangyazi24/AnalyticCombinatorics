import AnalyticCombinatorics.Ch4.Analytic.LogTransfer
import AnalyticCombinatorics.Ch4.Analytic.LogTransferBranch
import AnalyticCombinatorics.Ch4.Analytic.ComplexLogSeries

/-!
# Model faithfulness `hp_log` for the logarithmic transfer

Discharges the remaining hypothesis of `log_transfer_theorem_strong_remainder`:

  `logSingularityFun_hasFPowerSeriesAt : HasFPowerSeriesAt (logSingularityFun α) (toFMLS (logSingularityGF α)) 0`.

Route (ChatGPT-Pro R27): work directly via `hasFPowerSeriesAt_iff` and a per-`z` `HasSum`, avoiding the
absent `HasFPowerSeriesAt.mul`/FMLS multiplication and the radius computation.  The two factor series
(`oneSubCpowGF` from Mathlib's cpow series, `logGF` from `ComplexLogSeries`) are multiplied by an
ordinary Cauchy product (`hasSum_powerSeries_mul`), whose coefficient is `PowerSeries.coeff_mul`.
-/

open Complex Filter Asymptotics
open scoped Topology BigOperators ENNReal NNReal

namespace AnalyticCombinatorics

lemma logCoeffℂ_eq_inv (n : ℕ) : logCoeffℂ n = (n : ℂ)⁻¹ := by
  cases n <;> simp [logCoeffℂ]

/-- The `logGF` coefficient series is norm-summable on the unit ball. -/
lemma logGF_summable_norm {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ => ‖PowerSeries.coeff (R := ℂ) n logGF * z ^ n‖) := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    (summable_geometric_of_lt_one (norm_nonneg z) hz)
  rw [norm_mul, norm_pow, logGF, PowerSeries.coeff_mk, logCoeffℂ_eq_inv]
  rcases n with _ | m
  · simp
  · rw [norm_inv, Complex.norm_natCast]
    calc (((m + 1 : ℕ) : ℝ))⁻¹ * ‖z‖ ^ (m + 1)
        ≤ 1 * ‖z‖ ^ (m + 1) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          rw [inv_le_one_iff₀]; right; exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero m)
      _ = ‖z‖ ^ (m + 1) := one_mul _
      _ ≤ ‖z‖ ^ (m + 1) := le_rfl

/-- `logGF` realizes `-log(1-z)` on the unit ball. -/
lemma logGF_hasSum {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => PowerSeries.coeff (R := ℂ) n logGF * z ^ n) (-Complex.log (1 - z)) := by
  have hraw := AnalyticCombinatorics.hasSum_pow_succ_div_succ_neg_log (z := z) hz
  have hzero : PowerSeries.coeff (R := ℂ) 0 logGF * z ^ 0 = 0 := by
    simp [logGF, logCoeffℂ]
  have htail : HasSum
      (fun n : ℕ => PowerSeries.coeff (R := ℂ) (n + 1) logGF * z ^ (n + 1))
      (-Complex.log (1 - z)) := by
    have : (fun n : ℕ => PowerSeries.coeff (R := ℂ) (n + 1) logGF * z ^ (n + 1))
        = fun n : ℕ => z ^ (n + 1) / ((n + 1 : ℕ) : ℂ) := by
      funext n
      rw [logGF, PowerSeries.coeff_mk, logCoeffℂ_eq_inv]
      push_cast; ring
    rw [this]; exact hraw
  have hf0 : ∀ x ∉ Set.range Nat.succ,
      (fun n : ℕ => PowerSeries.coeff (R := ℂ) n logGF * z ^ n) x = 0 := by
    intro x hx
    rcases x with _ | m
    · simpa using hzero
    · exact absurd ⟨m, rfl⟩ hx
  exact (Function.Injective.hasSum_iff Nat.succ_injective hf0).mp htail

/-- The cpow factor `(1-z)^{-α}` realizes `oneSubCpowGF α` on the unit ball. -/
lemma oneSubCpowGF_hasSum {α z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => PowerSeries.coeff (R := ℂ) n (oneSubCpowGF α) * z ^ n)
      ((1 - z) ^ (-α)) := by
  have h := (Complex.one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero α)
  have hzball : z ∈ Metric.eball (0 : ℂ) 1 := by
    rw [mem_emetric_ball_zero_iff, enorm_eq_nnnorm]
    exact_mod_cast hz
  have hsum := h.hasSum hzball
  rw [Complex.cpow_neg, inv_eq_one_div]
  simpa [oneSubCpowGF, PowerSeries.coeff_mk, binCoeffℂ,
    FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, mul_comm, zero_add] using hsum

/-- The cpow factor series is norm-summable on the unit ball. -/
lemma oneSubCpowGF_summable_norm {α z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ => ‖PowerSeries.coeff (R := ℂ) n (oneSubCpowGF α) * z ^ n‖) := by
  have h := (Complex.one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero α)
  set p : FormalMultilinearSeries ℂ ℂ ℂ :=
    FormalMultilinearSeries.ofScalars ℂ (fun n => Ring.choose (α + n - 1) n) with hp
  have hlt : (‖z‖₊ : ℝ≥0∞) < p.radius := lt_of_lt_of_le (by exact_mod_cast hz) h.r_le
  refine (p.summable_norm_mul_pow hlt).congr (fun n => ?_)
  rw [norm_mul, norm_pow, hp, FormalMultilinearSeries.ofScalars_norm,
    oneSubCpowGF, PowerSeries.coeff_mk, binCoeffℂ, coe_nnnorm]

/-- **Cauchy product** for ordinary `PowerSeries ℂ` evaluated at `z`, in `HasSum` form.
Replaces the absent `HasFPowerSeriesAt.mul`. -/
lemma hasSum_powerSeries_mul (F G : PowerSeries ℂ) {z A B : ℂ}
    (hF : HasSum (fun n : ℕ => PowerSeries.coeff (R := ℂ) n F * z ^ n) A)
    (hG : HasSum (fun n : ℕ => PowerSeries.coeff (R := ℂ) n G * z ^ n) B)
    (habsF : Summable (fun n : ℕ => ‖PowerSeries.coeff (R := ℂ) n F * z ^ n‖))
    (habsG : Summable (fun n : ℕ => ‖PowerSeries.coeff (R := ℂ) n G * z ^ n‖)) :
    HasSum (fun n : ℕ => PowerSeries.coeff (R := ℂ) n (F * G) * z ^ n) (A * B) := by
  classical
  have hcoeff : ∀ n : ℕ,
      (∑ p ∈ Finset.antidiagonal n,
        (PowerSeries.coeff (R := ℂ) p.1 F * z ^ p.1) *
          (PowerSeries.coeff (R := ℂ) p.2 G * z ^ p.2))
        = PowerSeries.coeff (R := ℂ) n (F * G) * z ^ n := by
    intro n
    rw [PowerSeries.coeff_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [Finset.mem_antidiagonal] at hp
    rw [← hp, pow_add]; ring
  have hval : A * B
      = ∑' n : ℕ, PowerSeries.coeff (R := ℂ) n (F * G) * z ^ n := by
    rw [← hF.tsum_eq, ← hG.tsum_eq,
      tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm habsF habsG]
    exact tsum_congr hcoeff
  have hsummable : Summable (fun n : ℕ => PowerSeries.coeff (R := ℂ) n (F * G) * z ^ n) :=
    (summable_sum_mul_antidiagonal_of_summable_norm' habsF habsF.of_norm habsG habsG.of_norm).congr
      hcoeff
  rw [hval]; exact hsummable.hasSum

/-- **Discharges `hp_log`**: `logSingularityFun α` has power series `logSingularityGF α` at `0`. -/
theorem logSingularityFun_hasFPowerSeriesAt (α : ℂ) :
    HasFPowerSeriesAt (logSingularityFun α) (PowerSeries.toFMLS (logSingularityGF α)) 0 := by
  rw [hasFPowerSeriesAt_iff]
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with z hz
  have hz_norm : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hz
  have hprod := hasSum_powerSeries_mul (oneSubCpowGF α) logGF
    (oneSubCpowGF_hasSum (α := α) (z := z) hz_norm)
    (logGF_hasSum (z := z) hz_norm)
    (oneSubCpowGF_summable_norm (α := α) (z := z) hz_norm)
    (logGF_summable_norm (z := z) hz_norm)
  simpa [logSingularityGF, logSingularityFun, PowerSeries.coeff_toFMLS,
    smul_eq_mul, mul_comm] using hprod

/-- **Unconditional logarithmic singularity transfer (strong-remainder form).**
Discharges both faithfulness hypotheses of `log_transfer_theorem_strong_remainder`. -/
theorem log_transfer_theorem_strong_remainder_unconditional
    {α : ℝ} {C : ℂ} {R φ : ℝ} {f : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hα : 1 < α) (hC : C ≠ 0) (hR : 1 < R) (hφ0 : 0 < φ) (hφ2 : φ < Real.pi / 2)
    (hp : HasFPowerSeriesAt f p 0)
    (hΔ : AnalyticOnNhd ℂ f (DeltaDomainArg R φ))
    (hsing : Tendsto
      (fun z : ℂ => ‖f z - C * logSingularityFun (α : ℂ) z‖ * ‖(1 : ℂ) - z‖ ^ α)
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0)) :
    (fun n : ℕ => p.coeff n) ~[atTop]
      (fun n : ℕ => C * (((n : ℝ) ^ (α - 1) / Real.Gamma α * Real.log n : ℝ) : ℂ)) :=
  log_transfer_theorem_strong_remainder hα hC hR hφ0 hφ2 hp hΔ
    (logSingularityFun_hasFPowerSeriesAt (α : ℂ))
    (analyticOnNhd_logSingularityFun_deltaDomain hφ0 (by linarith [Real.pi_pos] : φ < Real.pi))
    hsing

end AnalyticCombinatorics
