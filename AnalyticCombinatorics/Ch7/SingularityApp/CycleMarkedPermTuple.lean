import AnalyticCombinatorics.Ch7.SingularityApp.CycleMarkedPermPairs
import AnalyticCombinatorics.Ch4.Analytic.OneSubCpowMul
import AnalyticCombinatorics.Ch2.EGF.LabelledPower

/-!
# The integer family of cycle-marked permutation tuples

`cycleMarkedPermPairClass` is the `k = 2` case of an integer family: a `k`-tuple of
permutations with one distinguished cycle in the first factor,

  `cycleMarkedPermTupleClass k := CYC(Z) ⋆ SET(CYC(Z))^{⋆k}`   (here `SET(CYC)=permutations`),

with EGF `log(1/(1-z))·(1-z)^{-k}` and hence, by the (banked) strong-remainder log
transfer at `α = k`, `C = 1`,

  `aₙ / n! ~ n^{k-1}/(k-1)! · log n`   (since `Γ(k) = (k-1)!`).

The only new ingredient over the `k = 2` file is the exponent law
`(mapℂ permutations.egf)^k = oneSubCpowGF k` (from `oneSubCpowGF_add`).
-/

open Complex Filter Asymptotics
open scoped BigOperators PowerSeries Topology

noncomputable section

namespace AnalyticCombinatorics

open AnalyticCombinatorics.Ch1
open AnalyticCombinatorics.Ch5.Meromorphic.Alignments

/-- A `k`-tuple of permutations with a distinguished cycle in the first factor. -/
def cycleMarkedPermTupleClass (k : ℕ) : CombClass :=
  CombClass.atom.lcyc.lprod (CombClass.permutations.lpow k)

/-- `(mapℂ permutations.egf)^k = oneSubCpowGF k` for `k ≥ 1`. -/
lemma mapℂ_permutations_egf_pow {k : ℕ} (hk : 1 ≤ k) :
    (PowerSeries.mapℂ CombClass.permutations.egf) ^ k = oneSubCpowGF (k : ℂ) := by
  have hone : PowerSeries.mapℂ CombClass.permutations.egf = oneSubCpowGF 1 := by
    ext n
    rw [coeff_mapℂ_permutations_egf, oneSubCpowGF, PowerSeries.coeff_mk, binCoeffℂ_one]
  induction k, hk using Nat.le_induction with
  | base => rw [pow_one, hone, Nat.cast_one]
  | succ m hm ih => rw [pow_succ, ih, hone, oneSubCpowGF_add, Nat.cast_add, Nat.cast_one]

/-- **Master EGF identity** for the tuple family: `mapℂ A.egf = logSingularityGF k`. -/
theorem mapℂ_cycleMarkedPermTupleClass_egf {k : ℕ} (hk : 1 ≤ k) :
    PowerSeries.mapℂ (cycleMarkedPermTupleClass k).egf = logSingularityGF (k : ℂ) := by
  have hprod : PowerSeries.mapℂ (cycleMarkedPermTupleClass k).egf
      = logGF * oneSubCpowGF (k : ℂ) := by
    rw [cycleMarkedPermTupleClass, CombClass.egf_lprod, CombClass.egf_lpow, map_mul, map_pow,
      atom_lcyc_egf_eq_cycleEGFℚ, map_cycleEGFℚ, mapℂ_permutations_egf_pow hk,
      ← logGF_eq_cycleEGFℂ]
  rw [hprod, logSingularityGF, mul_comm]

/-- **Integer family asymptotic**: `aₙ/n! ~ n^{k-1}/(k-1)!·log n` for `k ≥ 2`. -/
theorem cycleMarkedPermTupleClass_counts_div_factorial_isEquivalent {k : ℕ} (hk : 2 ≤ k) :
    (fun n : ℕ => ((cycleMarkedPermTupleClass k).counts n : ℝ) / (n.factorial : ℝ)) ~[atTop]
      (fun n : ℕ => (n : ℝ) ^ (k - 1) / ((k - 1).factorial : ℝ) * Real.log n) := by
  have hkR : (1 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hk1 : 1 ≤ k := by omega
  have hcast : ((k : ℝ) : ℂ) = (k : ℂ) := by norm_num
  have hsing : Tendsto
      (fun z : ℂ => ‖logSingularityFun ((k : ℝ) : ℂ) z
          - (1 : ℂ) * logSingularityFun ((k : ℝ) : ℂ) z‖ * ‖(1 : ℂ) - z‖ ^ (k : ℝ))
      (𝓝[DeltaDomainArg 2 (Real.pi / 4)] (1 : ℂ)) (𝓝 0) := by
    have hzero : (fun z : ℂ => ‖logSingularityFun ((k : ℝ) : ℂ) z
        - (1 : ℂ) * logSingularityFun ((k : ℝ) : ℂ) z‖ * ‖(1 : ℂ) - z‖ ^ (k : ℝ))
        = fun _ => 0 := by
      funext z; rw [one_mul, sub_self, norm_zero, zero_mul]
    rw [hzero]; exact tendsto_const_nhds
  have htransfer := log_transfer_theorem_strong_remainder_unconditional
    (α := (k : ℝ)) (C := (1 : ℂ)) (R := (2 : ℝ)) (φ := Real.pi / 4)
    (f := logSingularityFun ((k : ℝ) : ℂ))
    (p := PowerSeries.toFMLS (logSingularityGF ((k : ℝ) : ℂ)))
    hkR one_ne_zero (by norm_num) (by positivity) (by linarith [Real.pi_pos])
    (logSingularityFun_hasFPowerSeriesAt ((k : ℝ) : ℂ))
    (analyticOnNhd_logSingularityFun_deltaDomain (by positivity)
      (by linarith [Real.pi_pos]))
    hsing
  have hLHS : (fun n : ℕ => (PowerSeries.toFMLS (logSingularityGF ((k : ℝ) : ℂ))).coeff n)
      = (fun n : ℕ =>
          ((((cycleMarkedPermTupleClass k).counts n : ℝ) / (n.factorial : ℝ) : ℝ) : ℂ)) := by
    funext n
    rw [PowerSeries.coeff_toFMLS, hcast, ← mapℂ_cycleMarkedPermTupleClass_egf hk1,
      PowerSeries.coeff_mapℂ, CombClass.coeff_egf]
    push_cast; ring
  have hRHS : (fun n : ℕ => (1 : ℂ) *
        (((n : ℝ) ^ ((k : ℝ) - 1) / Real.Gamma (k : ℝ) * Real.log n : ℝ) : ℂ))
      = (fun n : ℕ => (((n : ℝ) ^ (k - 1) / ((k - 1).factorial : ℝ) * Real.log n : ℝ) : ℂ)) := by
    funext n
    have hΓ : Real.Gamma (k : ℝ) = ((k - 1).factorial : ℝ) := by
      have : (k : ℝ) = ((k - 1 : ℕ) : ℝ) + 1 := by
        have : k - 1 + 1 = k := by omega
        rw [← this]; push_cast; ring
      rw [this, Real.Gamma_nat_eq_factorial]
    have hpow : ((n : ℝ) ^ ((k : ℝ) - 1)) = (n : ℝ) ^ (k - 1) := by
      rw [show ((k : ℝ) - 1) = (((k - 1 : ℕ)) : ℝ) by
        have : k - 1 + 1 = k := by omega
        rw [← this]; push_cast; ring, Real.rpow_natCast]
    rw [one_mul, hΓ, hpow]
  rw [hLHS, hRHS] at htransfer
  exact ofReal_isEquivalent_iff.mp htransfer

end AnalyticCombinatorics
