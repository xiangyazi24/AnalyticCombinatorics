import AnalyticCombinatorics.Ch8.Partitions.CenterTracking
import AnalyticCombinatorics.Ch8.Partitions.ErdosConcrete
import AnalyticCombinatorics.Ch8.Partitions.ErdosLimit

/-!
# hhit via center-tracking: the gap-isolating interface

This is a *structural* brick, NOT a closure of `hhit`.  It packages the §9 convergence engine
`tendsto_of_center_tracking` for the concrete killed-harmonic hit value `hitVal Pker rnk J u`, so that
the remaining analytic content is exactly the explicit hypothesis `hdata`:

  for cofinitely many cutoffs `J`, there exist a center sequence `c` and a tracking bound `V` with
  * `V → 0`                         (the *tracking* error — may be only polynomial, e.g. `R^{-1/2}`),
  * `∑_R |c(R+1) − c R| < ∞`        (the *center links* — must be summable), and
  * `|hitVal_J(n) − c(rnk n)| ≤ V(rnk n)`.

The design audit (ChatGPT R1/R2, 2026-06-13) established that the coupling/FK route supplies the
*tracking* bound at a polynomial (non-summable) rate, while the *summable center links* require a
separate finite-boundary renewal / kernel-gradient estimate that is NOT derivable from the banked
first-moment drift `muTilde_two_term`.  This interface isolates that single remaining input.  See
`HANDOFF/TASK9-gap.md`.
-/

noncomputable section

open Filter Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- **`hhit` from eventual center-tracking of `hitVal`.**  If, for cofinitely many cutoffs `J`, the
killed-harmonic hit value tracks a center sequence with a vanishing error and summable center links,
then `hitVal Pker rnk J u` converges for cofinitely many `J` (i.e. `hhit` holds).  Immediate from
`tendsto_of_center_tracking`; the content is entirely in `hdata`. -/
theorem hhit_of_eventual_center_tracking_hitVal
    (hdata : ∀ᶠ J : ℕ in atTop,
        ∃ c V : ℕ → ℝ,
          Tendsto V atTop (𝓝 0) ∧
          Summable (fun R => |c (R + 1) - c R|) ∧
          (∀ n, |hitVal Pker rnk J u n - c (rnk n)| ≤ V (rnk n))) :
    ∀ᶠ J : ℕ in atTop,
        ∃ L : ℝ, Tendsto (fun n => hitVal Pker rnk J u n) atTop (𝓝 L) := by
  filter_upwards [hdata] with J hJ
  obtain ⟨c, V, hVtend, hlink, htrack⟩ := hJ
  exact tendsto_of_center_tracking hVtend hlink htrack rnk_tendsto_atTop

/-- Composing with the banked reduction: eventual center-tracking of `hitVal` ⟹ the unconditional
Hardy–Ramanujan partition-ratio limit. -/
theorem erdos_partition_limit_exists_of_center_tracking
    (hdata : ∀ᶠ J : ℕ in atTop,
        ∃ c V : ℕ → ℝ,
          Tendsto V atTop (𝓝 0) ∧
          Summable (fun R => |c (R + 1) - c R|) ∧
          (∀ n, |hitVal Pker rnk J u n - c (rnk n)| ≤ V (rnk n))) :
    ∃ a : ℝ, 0 < a ∧ Tendsto u atTop (𝓝 a) :=
  erdos_partition_limit_exists_of_hit (hhit_of_eventual_center_tracking_hitVal hdata)

#print axioms hhit_of_eventual_center_tracking_hitVal
#print axioms erdos_partition_limit_exists_of_center_tracking

end AnalyticCombinatorics.Ch8.Partitions.Erdos
