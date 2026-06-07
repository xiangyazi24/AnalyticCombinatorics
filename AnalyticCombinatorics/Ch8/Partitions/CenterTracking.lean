import Mathlib

/-!
# R7 Fact B via Doeblin: the §9 convergence engine

The deterministic core of the block-oscillation → convergence connection.  If the tail-sup of block
oscillation `V` is summable, the block-centers `c` have summable consecutive links (`|c(R+1)−c R| ≤
V R`) hence converge to some `L`, and `h` tracks the centers (`|h n − c(rank n)| ≤ V(rank n) → 0`), so
`h → L`.  This avoids the far-pair overlap obstruction entirely: only the *monotone* tail-sup `V`
needs to contract (geometrically), which it does because the local contraction dominates it.
Opus-authored.
-/

noncomputable section

open Filter Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- **§9 convergence engine.** Summable tail-sup `V` + center links + center-tracking ⟹ `h` converges. -/
theorem tendsto_of_center_tracking {h c V : ℕ → ℝ} {rank : ℕ → ℕ}
    (hVtend : Tendsto V atTop (𝓝 0))
    (hlink_sum : Summable (fun R => |c (R + 1) - c R|))
    (htrack : ∀ n, |h n - c (rank n)| ≤ V (rank n))
    (hrank : Tendsto rank atTop atTop) :
    ∃ L : ℝ, Tendsto h atTop (𝓝 L) := by
  -- centers are Cauchy: consecutive distances are summable
  have hdist_sum : Summable (fun R => dist (c R) (c (R + 1))) := by
    simpa [Real.dist_eq, abs_sub_comm] using hlink_sum
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist hdist_sum)
  refine ⟨L, ?_⟩
  have h1 : Tendsto (fun n => c (rank n)) atTop (𝓝 L) := hL.comp hrank
  have h2 : Tendsto (fun n => h n - c (rank n)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) (hVtend.comp hrank)
    simpa [Real.norm_eq_abs] using htrack n
  have hsum := h1.add h2
  simpa using hsum

end AnalyticCombinatorics.Ch8.Partitions.Erdos
