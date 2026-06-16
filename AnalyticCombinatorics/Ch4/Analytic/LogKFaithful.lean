import AnalyticCombinatorics.Ch4.Analytic.LogKCoeff
import AnalyticCombinatorics.Ch4.Analytic.LogFaithful

/-!
# Faithfulness and Δ-analyticity for the fixed `log^k` hierarchy

`logKGF α k` is the formal model for

`(1 - z)^(-α) * (-log (1 - z))^k`.

This file proves the analytic faithfulness layer by induction on `k`, reusing the same
Cauchy-product bridge used for the one-log and two-log models.
-/

noncomputable section

open Complex Filter Asymptotics
open scoped Topology BigOperators

/-- The fixed-`k` logarithmic singularity model
`(1 - z)^(-α) * (-log (1 - z))^k`. -/
noncomputable def logKSingularityFun (α : ℂ) (k : ℕ) : ℂ → ℂ :=
  fun z => (1 - z) ^ (-α) * (-Complex.log (1 - z)) ^ k

namespace AnalyticCombinatorics

private lemma logKGF_zero_eq (α : ℂ) :
    logKGF α 0 = oneSubCpowGF α := by
  simp [logKGF]

private lemma logKGF_succ_eq (α : ℂ) (k : ℕ) :
    logKGF α (Nat.succ k) = logKGF α k * logGF := by
  simp [logKGF]

/-- Norm-summability of the fixed-`k` logarithmic model coefficient series on the unit ball. -/
lemma logKGF_summable_norm {α z : ℂ} (hz : ‖z‖ < 1) (k : ℕ) :
    Summable (fun n : ℕ => ‖PowerSeries.coeff (R := ℂ) n (logKGF α k) * z ^ n‖) := by
  classical
  induction k with
  | zero =>
      simpa [logKGF_zero_eq] using oneSubCpowGF_summable_norm (α := α) (z := z) hz
  | succ k ih =>
      have hF : Summable
          (fun n : ℕ => ‖PowerSeries.coeff (R := ℂ) n (logKGF α k) * z ^ n‖) := ih
      have hG : Summable
          (fun n : ℕ => ‖PowerSeries.coeff (R := ℂ) n logGF * z ^ n‖) :=
        logGF_summable_norm (z := z) hz
      have hFn : Summable
          (fun j : ℕ => ‖‖PowerSeries.coeff (R := ℂ) j (logKGF α k) * z ^ j‖‖) := by
        simpa using hF
      have hGn : Summable
          (fun j : ℕ => ‖‖PowerSeries.coeff (R := ℂ) j logGF * z ^ j‖‖) := by
        simpa using hG
      have hbig := summable_sum_mul_antidiagonal_of_summable_norm' hFn hF hGn hG
      refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hbig
      rw [logKGF_succ_eq (α := α) (k := k), PowerSeries.coeff_mul, Finset.sum_mul]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p hp => ?_)
      rw [Finset.mem_antidiagonal] at hp
      have heq :
          PowerSeries.coeff (R := ℂ) p.1 (logKGF α k) *
              PowerSeries.coeff (R := ℂ) p.2 logGF * z ^ n
            =
          (PowerSeries.coeff (R := ℂ) p.1 (logKGF α k) * z ^ p.1) *
              (PowerSeries.coeff (R := ℂ) p.2 logGF * z ^ p.2) := by
        rw [← hp, pow_add]
        ring
      rw [heq, norm_mul]

/-- The fixed-`k` logarithmic model coefficient series realizes
`(1-z)^(-α) * (-log(1-z))^k` on the unit ball. -/
lemma logKGF_hasSum {α z : ℂ} (hz : ‖z‖ < 1) (k : ℕ) :
    HasSum
      (fun n : ℕ => PowerSeries.coeff (R := ℂ) n (logKGF α k) * z ^ n)
      ((1 - z) ^ (-α) * (-Complex.log (1 - z)) ^ k) := by
  classical
  induction k with
  | zero =>
      have h := oneSubCpowGF_hasSum (α := α) (z := z) hz
      simpa [logKGF_zero_eq] using h
  | succ k ih =>
      have hprod := hasSum_powerSeries_mul (logKGF α k) logGF
        ih
        (logGF_hasSum (z := z) hz)
        (logKGF_summable_norm (α := α) (z := z) hz k)
        (logGF_summable_norm (z := z) hz)
      simpa [logKGF_succ_eq, pow_succ, mul_assoc] using hprod

/-- Faithfulness: `logKSingularityFun α k` has power series `logKGF α k` at `0`. -/
theorem logKSingularityFun_hasFPowerSeriesAt (α : ℂ) (k : ℕ) :
    HasFPowerSeriesAt (logKSingularityFun α k) (PowerSeries.toFMLS (logKGF α k)) 0 := by
  rw [hasFPowerSeriesAt_iff]
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with z hz
  have hz_norm : ‖z‖ < 1 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hz
  have h := logKGF_hasSum (α := α) (z := z) hz_norm k
  simpa [logKSingularityFun, PowerSeries.coeff_toFMLS, smul_eq_mul, mul_comm] using h

/-- Δ-analyticity of the fixed-`k` logarithmic model. -/
theorem analyticOnNhd_logKSingularityFun_deltaDomain {α : ℂ} {R φ : ℝ}
    (k : ℕ) (hφ0 : 0 < φ) (hφπ : φ < Real.pi) :
    AnalyticOnNhd ℂ (logKSingularityFun α k) (DeltaDomainArg R φ) := by
  have hpow : AnalyticOnNhd ℂ (fun z : ℂ => (1 - z) ^ (-α)) (DeltaDomainArg R φ) :=
    analyticOnNhd_one_sub_cpow_deltaDomain (α := α) (R := R) (φ := φ) hφ0 hφπ
  have hlog : AnalyticOnNhd ℂ (fun z : ℂ => -Complex.log (1 - z)) (DeltaDomainArg R φ) :=
    analyticOnNhd_negLog_one_sub_deltaDomain (R := R) (φ := φ) hφ0
  simpa [logKSingularityFun] using hpow.mul (hlog.pow k)

end AnalyticCombinatorics
