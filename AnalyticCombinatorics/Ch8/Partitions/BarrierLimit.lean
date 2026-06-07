import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.MassRateApprox2
import AnalyticCombinatorics.Ch8.Partitions.BarrierHarmonic
import AnalyticCombinatorics.Ch8.Partitions.BarrierInduction

/-!
# Mass-rate campaign: §7 unconditional barrier bounds on `u`

The banked kernel-mass rate in `o(slack)` form (`kernelMass_rate_vs_slack`) discharges the
hypotheses of the conditional barrier theorems, giving unconditionally that the normalized
partition function `u` is bounded above (`u_limsup_finite`) and bounded below away from `0`
(`u_liminf_positive`).  Opus-authored.
-/

noncomputable section

open Filter
open scoped Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- **`u` is bounded above** (R6): unconditional, via the superharmonic upper barrier fed by the
`o(slack)` mass rate. -/
theorem u_limsup_finite : ∃ M : ℝ, 0 < M ∧ ∀ᶠ n : ℕ in atTop, u n ≤ M := by
  obtain ⟨A, δ, hA, hδ, hpos, hsuper⟩ :=
    upperBarrier_kernel_superharmonic_of_rate (le_refl (3:ℝ))
      (kernelMass_rate_vs_slack (le_refl (3:ℝ)))
  exact u_limsup_finite_of_superharmonic hA (le_refl (3:ℝ)) hδ hpos hsuper

/-- **`u` is bounded below away from 0** (R6): unconditional, via the subharmonic lower barrier fed
by the `o(slack)` mass rate. -/
theorem u_liminf_positive : ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, c ≤ u n := by
  obtain ⟨A, δ, hA, hδ, hsub⟩ :=
    lowerBarrier_kernel_subharmonic_of_rate (le_refl (3:ℝ))
      (kernelMass_rate_vs_slack (le_refl (3:ℝ)))
  exact u_liminf_positive_of_subharmonic hA (le_refl (3:ℝ)) hδ hsub

end AnalyticCombinatorics.Ch8.Partitions.Erdos
