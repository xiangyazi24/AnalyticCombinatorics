import AnalyticCombinatorics.Ch7.SingularityApp.CycleMarkedPermPairs
import AnalyticCombinatorics.Ch4.Analytic.OneSubCpowMul
import AnalyticCombinatorics.Ch4.Analytic.LogSqTransfer

/-!
# A genuine `n·(log n)²` species: pairs of permutations each with a marked cycle

The labelled class

  `cycleMarkedPermPairBothClass := cycleMarkedPermClass ⋆ cycleMarkedPermClass`

— an ordered pair of permutations, each carrying one distinguished cycle — has EGF

  `(log(1/(1-z)))²·(1-z)^{-2} = (1-z)^{-2}·(-log(1-z))² = logSqGF 2`.

By the (banked) squared-logarithm transfer at `α = 2`, `C = 1` (zero remainder, `Γ(2)=1`),

  `aₙ / n! ~ n·(log n)²`.

This is the first combinatorial application of the `log²` transfer (the analog of the
cycle-marked permutation pairs for the one-log transfer).
-/

open Complex Filter Asymptotics
open scoped BigOperators PowerSeries Topology

noncomputable section

namespace AnalyticCombinatorics

open AnalyticCombinatorics.Ch1
open AnalyticCombinatorics.Ch5.Meromorphic.Alignments

/-- A pair of permutations, each with one distinguished cycle. -/
def cycleMarkedPermPairBothClass : CombClass :=
  cycleMarkedPermClass.lprod cycleMarkedPermClass

/-- `mapℂ` of a permutation-with-marked-cycle EGF is `logGF · (1-z)^{-1}`. -/
lemma mapℂ_cycleMarkedPermClass_egf :
    PowerSeries.mapℂ cycleMarkedPermClass.egf = logGF * oneSubCpowGF 1 := by
  rw [cycleMarkedPermClass, CombClass.egf_lprod, map_mul, atom_lcyc_egf_eq_cycleEGFℚ,
    map_cycleEGFℚ, ← logGF_eq_cycleEGFℂ]
  congr 1
  ext n
  rw [coeff_mapℂ_permutations_egf, oneSubCpowGF, PowerSeries.coeff_mk, binCoeffℂ_one]

/-- **Master EGF identity**: `mapℂ A.egf = logSqGF 2`. -/
theorem mapℂ_cycleMarkedPermPairBothClass_egf :
    PowerSeries.mapℂ cycleMarkedPermPairBothClass.egf = logSqGF 2 := by
  rw [cycleMarkedPermPairBothClass, CombClass.egf_lprod, map_mul, mapℂ_cycleMarkedPermClass_egf,
    logSqGF, logSingularityGF,
    show oneSubCpowGF (2 : ℂ) = oneSubCpowGF 1 * oneSubCpowGF 1 by
      rw [oneSubCpowGF_add]; norm_num]
  ring

/-- **`n·(log n)²` asymptotic** for pairs of permutations each with a distinguished cycle. -/
theorem cycleMarkedPermPairBothClass_counts_div_factorial_isEquivalent :
    (fun n : ℕ => (cycleMarkedPermPairBothClass.counts n : ℝ) / (n.factorial : ℝ)) ~[atTop]
      (fun n : ℕ => (n : ℝ) * (Real.log n) ^ 2) := by
  have hsing : Tendsto
      (fun z : ℂ => ‖logSqSingularityFun ((2 : ℝ) : ℂ) z
          - (1 : ℂ) * logSqSingularityFun ((2 : ℝ) : ℂ) z‖ * ‖(1 : ℂ) - z‖ ^ (2 : ℝ))
      (𝓝[DeltaDomainArg 2 (Real.pi / 4)] (1 : ℂ)) (𝓝 0) := by
    have hzero : (fun z : ℂ => ‖logSqSingularityFun ((2 : ℝ) : ℂ) z
        - (1 : ℂ) * logSqSingularityFun ((2 : ℝ) : ℂ) z‖ * ‖(1 : ℂ) - z‖ ^ (2 : ℝ))
        = fun _ => 0 := by
      funext z; rw [one_mul, sub_self, norm_zero, zero_mul]
    rw [hzero]; exact tendsto_const_nhds
  have htransfer := logSq_transfer_theorem_strong_remainder_unconditional
    (α := (2 : ℝ)) (C := (1 : ℂ)) (R := (2 : ℝ)) (φ := Real.pi / 4)
    (f := logSqSingularityFun ((2 : ℝ) : ℂ))
    (p := PowerSeries.toFMLS (logSqGF ((2 : ℝ) : ℂ)))
    (by norm_num) one_ne_zero (by norm_num) (by positivity) (by linarith [Real.pi_pos])
    (logSqSingularityFun_hasFPowerSeriesAt ((2 : ℝ) : ℂ))
    (analyticOnNhd_logSqSingularityFun_deltaDomain (by positivity) (by linarith [Real.pi_pos]))
    hsing
  have hLHS : (fun n : ℕ => (PowerSeries.toFMLS (logSqGF ((2 : ℝ) : ℂ))).coeff n)
      = (fun n : ℕ =>
          (((cycleMarkedPermPairBothClass.counts n : ℝ) / (n.factorial : ℝ) : ℝ) : ℂ)) := by
    funext n
    rw [PowerSeries.coeff_toFMLS, show ((2 : ℝ) : ℂ) = (2 : ℂ) by norm_num,
      ← mapℂ_cycleMarkedPermPairBothClass_egf, PowerSeries.coeff_mapℂ, CombClass.coeff_egf]
    push_cast; ring
  have hRHS : (fun n : ℕ => (1 : ℂ) *
        (((n : ℝ) ^ ((2 : ℝ) - 1) / Real.Gamma 2 * (Real.log n) ^ 2 : ℝ) : ℂ))
      = (fun n : ℕ => (((n : ℝ) * (Real.log n) ^ 2 : ℝ) : ℂ)) := by
    funext n
    rw [one_mul, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.Gamma_two, div_one]
  rw [hLHS, hRHS] at htransfer
  exact ofReal_isEquivalent_iff.mp htransfer

end AnalyticCombinatorics
