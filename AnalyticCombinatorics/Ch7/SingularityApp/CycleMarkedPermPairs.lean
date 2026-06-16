import Mathlib
import AnalyticCombinatorics.Ch2.EGF.LabelledProduct
import AnalyticCombinatorics.Ch5.Meromorphic.Alignments
import AnalyticCombinatorics.Ch4.Analytic.LogFaithful

/-!
# A genuine labelled class with an `n log n` coefficient asymptotic

The labelled class

  `cycleMarkedPermPairClass := (CYC ⋆ SET(CYC)) ⋆ SET(CYC)`

— an ordered pair of permutations in which one cycle of the first permutation is
distinguished — has exponential generating function

  `A(z) = log(1/(1-z)) · 1/(1-z)² = (1-z)^{-2} · (-log(1-z))`,

which is exactly the logarithmic-singularity model `logSingularityFun 2`.  By the
unconditional strong-remainder logarithmic transfer
(`log_transfer_theorem_strong_remainder_unconditional`) at the clean point
`α = 2`, `C = 1`, with *zero* singular remainder, its normalized coefficients
satisfy

  `aₙ / n! ~ n · log n`   (since `Γ(2) = 1`).

This is the first application of the new unconditional log transfer to a genuine
labelled species.  All the analysis is banked: the only new work is
labelled-class / EGF plumbing, which reduces to the formal identity
`mapℂ A.egf = logSingularityGF 2`.
-/

open Complex Filter Asymptotics
open scoped BigOperators PowerSeries Topology

noncomputable section

namespace AnalyticCombinatorics

open AnalyticCombinatorics.Ch1
open AnalyticCombinatorics.Ch5.Meromorphic.Alignments

/-- A permutation with one distinguished cycle: a single labelled cycle (`atom.lcyc`)
attached to an arbitrary permutation of the remaining labels.  EGF `log(1/(1-z))·1/(1-z)`. -/
def cycleMarkedPermClass : CombClass :=
  CombClass.atom.lcyc.lprod CombClass.permutations

/-- An ordered pair: a cycle-marked permutation together with a second permutation.
EGF `log(1/(1-z))·1/(1-z)² = (1-z)^{-2}·(-log(1-z))`. -/
def cycleMarkedPermPairClass : CombClass :=
  cycleMarkedPermClass.lprod CombClass.permutations

/-! ### Formal EGF identity `mapℂ A.egf = logSingularityGF 2` -/

/-- Over `ℂ`, the permutation EGF has all coefficients `1` (it is `(1-z)^{-1}`). -/
lemma coeff_mapℂ_permutations_egf (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n (PowerSeries.mapℂ CombClass.permutations.egf) = 1 := by
  have h1 : PowerSeries.coeff (R := ℚ) n CombClass.permutations.egf = 1 := by
    rw [CombClass.coeff_egf, CombClass.counts_permutations,
      div_self (by exact_mod_cast Nat.factorial_ne_zero n)]
  rw [PowerSeries.coeff_mapℂ, h1, map_one]

/-- `logGF` (the `-log(1-z)` series) coincides with the labelled-cycle EGF `cycleEGFℂ`. -/
lemma logGF_eq_cycleEGFℂ : logGF = cycleEGFℂ := by
  ext n
  rw [logGF, PowerSeries.coeff_mk, coeff_cycleEGFℂ, logCoeffℂ]
  split_ifs with h
  · rw [h]; simp
  · rfl

/-- The binomial coefficients of `(1-z)^{-2}` are `n + 1`. -/
lemma binCoeffℂ_two (n : ℕ) : binCoeffℂ 2 n = (n : ℂ) + 1 := by
  induction n with
  | zero => simp [binCoeffℂ]
  | succ k ih =>
    have hrec := binCoeffℂ_succ 2 k
    rw [ih] at hrec
    have hk1 : ((k : ℂ) + 1) ≠ 0 := by
      have : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have h2 : ((k : ℝ) + 1 : ℂ) ≠ 0 := by exact_mod_cast this.ne'
      push_cast at h2 ⊢; exact h2
    have hcomm : (2 + (k : ℂ)) * ((k : ℂ) + 1) = ((k : ℂ) + 1) * (2 + (k : ℂ)) := by ring
    rw [hcomm] at hrec
    have hb : binCoeffℂ 2 (k + 1) = 2 + (k : ℂ) := mul_left_cancel₀ hk1 hrec
    rw [hb]; push_cast; ring

/-- The product of two permutation EGFs is `(1-z)^{-2}`, i.e. `oneSubCpowGF 2`. -/
lemma mapℂ_perm_sq_eq_oneSubCpowGF_two :
    PowerSeries.mapℂ CombClass.permutations.egf *
        PowerSeries.mapℂ CombClass.permutations.egf
      = oneSubCpowGF 2 := by
  ext n
  rw [PowerSeries.coeff_mul, oneSubCpowGF, PowerSeries.coeff_mk, binCoeffℂ_two]
  have hterm : ∀ p ∈ Finset.antidiagonal n,
      PowerSeries.coeff (R := ℂ) p.1 (PowerSeries.mapℂ CombClass.permutations.egf) *
        PowerSeries.coeff (R := ℂ) p.2 (PowerSeries.mapℂ CombClass.permutations.egf) = 1 := by
    intro p _
    rw [coeff_mapℂ_permutations_egf, coeff_mapℂ_permutations_egf, mul_one]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.Nat.card_antidiagonal,
    nsmul_eq_mul, mul_one]
  push_cast; ring

/-- **Master EGF identity.** The complex EGF of the cycle-marked permutation-pair class
is the logarithmic-singularity generating function `(1-z)^{-2}·(-log(1-z))` at `α = 2`. -/
theorem mapℂ_cycleMarkedPermPairClass_egf :
    PowerSeries.mapℂ cycleMarkedPermPairClass.egf = logSingularityGF 2 := by
  rw [cycleMarkedPermPairClass, cycleMarkedPermClass,
    CombClass.egf_lprod, CombClass.egf_lprod, map_mul, map_mul,
    atom_lcyc_egf_eq_cycleEGFℚ, map_cycleEGFℚ, logSingularityGF, logGF_eq_cycleEGFℂ,
    mul_assoc, mapℂ_perm_sq_eq_oneSubCpowGF_two, mul_comm]

/-! ### The `n log n` coefficient asymptotic via the unconditional log transfer -/

/-- **First application of the unconditional logarithmic transfer to a genuine labelled
species.** The normalized counts of the cycle-marked permutation-pair class satisfy
`aₙ / n! ~ n · log n`. -/
theorem cycleMarkedPermPairClass_counts_div_factorial_isEquivalent :
    (fun n : ℕ => (cycleMarkedPermPairClass.counts n : ℝ) / (n.factorial : ℝ)) ~[atTop]
      (fun n : ℕ => (n : ℝ) * Real.log n) := by
  -- The singular remainder is identically zero: `f - 1·f = 0`.
  have hsing : Tendsto
      (fun z : ℂ => ‖logSingularityFun ((2 : ℝ) : ℂ) z
          - (1 : ℂ) * logSingularityFun ((2 : ℝ) : ℂ) z‖ * ‖(1 : ℂ) - z‖ ^ (2 : ℝ))
      (𝓝[DeltaDomainArg 2 (Real.pi / 4)] (1 : ℂ)) (𝓝 0) := by
    have hzero : (fun z : ℂ => ‖logSingularityFun ((2 : ℝ) : ℂ) z
        - (1 : ℂ) * logSingularityFun ((2 : ℝ) : ℂ) z‖ * ‖(1 : ℂ) - z‖ ^ (2 : ℝ))
        = fun _ => 0 := by
      funext z; rw [one_mul, sub_self, norm_zero, zero_mul]
    rw [hzero]; exact tendsto_const_nhds
  have htransfer := log_transfer_theorem_strong_remainder_unconditional
    (α := (2 : ℝ)) (C := (1 : ℂ)) (R := (2 : ℝ)) (φ := Real.pi / 4)
    (f := logSingularityFun ((2 : ℝ) : ℂ))
    (p := PowerSeries.toFMLS (logSingularityGF ((2 : ℝ) : ℂ)))
    (by norm_num) one_ne_zero (by norm_num)
    (by positivity) (by linarith [Real.pi_pos])
    (logSingularityFun_hasFPowerSeriesAt ((2 : ℝ) : ℂ))
    (analyticOnNhd_logSingularityFun_deltaDomain (by positivity)
      (by linarith [Real.pi_pos]))
    hsing
  -- Rewrite the transfer conclusion into the genuine count / target form.
  have hLHS : (fun n : ℕ => (PowerSeries.toFMLS (logSingularityGF ((2 : ℝ) : ℂ))).coeff n)
      = (fun n : ℕ => (((cycleMarkedPermPairClass.counts n : ℝ) / (n.factorial : ℝ) : ℝ) : ℂ)) := by
    funext n
    rw [PowerSeries.coeff_toFMLS, show ((2 : ℝ) : ℂ) = (2 : ℂ) by norm_num,
      ← mapℂ_cycleMarkedPermPairClass_egf, PowerSeries.coeff_mapℂ, CombClass.coeff_egf]
    push_cast; ring
  have hRHS : (fun n : ℕ => (1 : ℂ) *
        (((n : ℝ) ^ ((2 : ℝ) - 1) / Real.Gamma 2 * Real.log n : ℝ) : ℂ))
      = (fun n : ℕ => (((n : ℝ) * Real.log n : ℝ) : ℂ)) := by
    funext n
    rw [one_mul]
    congr 1
    rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.Gamma_two, div_one]
  rw [hLHS, hRHS] at htransfer
  exact ofReal_isEquivalent_iff.mp htransfer

end AnalyticCombinatorics
