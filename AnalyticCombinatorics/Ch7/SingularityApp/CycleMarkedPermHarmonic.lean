import AnalyticCombinatorics.Ch4.Analytic.LogAlphaOneTransfer
import AnalyticCombinatorics.Ch7.SingularityApp.CycleMarkedPermPairBoth

noncomputable section

open Complex Filter Asymptotics
open scoped Topology BigOperators PowerSeries

namespace AnalyticCombinatorics

open AnalyticCombinatorics.Ch1
open AnalyticCombinatorics.Ch5.Meromorphic.Alignments

/-- The normalized counts of permutations with one distinguished cycle satisfy `aₙ/n! ~ log n`. -/
theorem cycleMarkedPermClass_counts_div_factorial_isEquivalent :
    (fun n : ℕ => (cycleMarkedPermClass.counts n : ℝ) / (n.factorial : ℝ)) ~[atTop]
      (fun n : ℕ => Real.log n) := by
  set R : ℝ := 2 with hR_def
  set φ : ℝ := Real.pi / 4 with hφ_def
  have hφ0 : 0 < φ := by rw [hφ_def]; positivity
  have hφ2 : φ < Real.pi / 2 := by rw [hφ_def]; linarith [Real.pi_pos]
  have hφπ : φ < Real.pi := by linarith [Real.pi_pos]
  have hmap : PowerSeries.mapℂ cycleMarkedPermClass.egf = logSingularityGF (1 : ℂ) := by
    rw [mapℂ_cycleMarkedPermClass_egf, logSingularityGF, mul_comm]
  have hfaith : HasFPowerSeriesAt (logSingularityFun (1 : ℂ))
      (PowerSeries.toFMLS (PowerSeries.mapℂ cycleMarkedPermClass.egf)) 0 := by
    rw [hmap]
    exact logSingularityFun_hasFPowerSeriesAt (1 : ℂ)
  have hsing : Tendsto
      (fun z : ℂ => ‖logSingularityFun (1 : ℂ) z
          - (1 : ℂ) * logSingularityFun (1 : ℂ) z‖ * ‖(1 : ℂ) - z‖)
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0) := by
    have hzero : (fun z : ℂ => ‖logSingularityFun (1 : ℂ) z
        - (1 : ℂ) * logSingularityFun (1 : ℂ) z‖ * ‖(1 : ℂ) - z‖)
        = fun _ : ℂ => (0 : ℝ) := by
      funext z
      rw [one_mul, sub_self, norm_zero, zero_mul]
    rw [hzero]
    exact tendsto_const_nhds
  have htransfer := log_transfer_alpha_eq_one_strong_remainder
    (C := (1 : ℂ)) (R := R) (φ := φ)
    (f := logSingularityFun (1 : ℂ))
    (p := PowerSeries.toFMLS (PowerSeries.mapℂ cycleMarkedPermClass.egf))
    one_ne_zero (by rw [hR_def]; norm_num) hφ0 hφ2
    hfaith
    (analyticOnNhd_logSingularityFun_deltaDomain
      (α := (1 : ℂ)) (R := R) (φ := φ) hφ0 hφπ)
    hsing
  have hLHS : (fun n : ℕ =>
        (PowerSeries.toFMLS (PowerSeries.mapℂ cycleMarkedPermClass.egf)).coeff n)
      = (fun n : ℕ =>
        (((cycleMarkedPermClass.counts n : ℝ) / (n.factorial : ℝ) : ℝ) : ℂ)) := by
    funext n
    rw [PowerSeries.coeff_toFMLS, PowerSeries.coeff_mapℂ, CombClass.coeff_egf]
    push_cast
    ring
  have hRHS : (fun n : ℕ => (1 : ℂ) * (((Real.log n : ℝ) : ℂ)))
      = (fun n : ℕ => (((Real.log n : ℝ) : ℂ))) := by
    funext n
    rw [one_mul]
  rw [hLHS, hRHS] at htransfer
  exact ofReal_isEquivalent_iff.mp htransfer

end AnalyticCombinatorics
