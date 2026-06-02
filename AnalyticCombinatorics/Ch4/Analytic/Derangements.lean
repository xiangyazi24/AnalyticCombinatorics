import Mathlib.Combinatorics.Derangements.Exponential
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-!
# Derangement asymptotics

This file records the classical estimate `D_n ~ n! / e`, using Mathlib's
derangement probability limit.
-/

open Filter Asymptotics
open scoped Topology

/-- The probability that a permutation of `n` elements is a derangement tends to `1 / e`. -/
theorem derangement_prob_tendsto :
    Tendsto (fun n : ℕ => (numDerangements n : ℝ) / n.factorial) atTop
      (𝓝 (Real.exp (-1))) :=
  numDerangements_tendsto_inv_e

/-- The classical derangement asymptotic `D_n ~ n! / e`. -/
theorem numDerangements_isEquivalent :
    (fun n : ℕ => (numDerangements n : ℝ)) ~[atTop]
      (fun n : ℕ => (n.factorial : ℝ) * Real.exp (-1)) := by
  apply isEquivalent_of_tendsto_one
  have hlim :
      Tendsto
        (fun n : ℕ => ((numDerangements n : ℝ) / n.factorial) / Real.exp (-1))
        atTop (𝓝 1) := by
    simpa [Real.exp_ne_zero] using derangement_prob_tendsto.div_const (Real.exp (-1))
  refine Tendsto.congr' ?_ hlim
  exact Eventually.of_forall fun n => by
    dsimp
    have hn : (n.factorial : ℝ) ≠ 0 := by
      positivity
    field_simp [hn, Real.exp_ne_zero]
