import AnalyticCombinatorics.Ch8.Partitions.CenterTracking

/-!
# R7 Fact B via Doeblin: comparable-pair contraction ⟹ convergence (center-tracking packaging)

The far-pair obstruction is resolved by center-tracking: it suffices to control *comparable*-rank
oscillation (block centers `c` and a block-oscillation bound `V`), with far pairs handled by the
summable center links.  This lemma packages `tendsto_of_center_tracking` into the form produced by the
windowed-coupling ITER: a summable block-oscillation bound `V → 0` with `|h n − c(rank n)| ≤ V(rank n)`
(tracking) and adjacent centers `|c(R+1) − c R| ≤ V R` forces `h` to converge.  Opus-authored.
-/

noncomputable section

open Filter Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- **Comparable-pair contraction ⟹ convergence.** A summable, vanishing block-oscillation bound `V`
that tracks `h` to its block centers `c` (with adjacent centers within `V`) forces `h` to converge. -/
theorem tendsto_of_comparable_contraction {h c V : ℕ → ℝ} {rank : ℕ → ℕ}
    (hrank : Tendsto rank atTop atTop)
    (hVtend : Tendsto V atTop (𝓝 0))
    (hVsum : Summable V)
    (htrack : ∀ n, |h n - c (rank n)| ≤ V (rank n))
    (hlink : ∀ R, |c (R + 1) - c R| ≤ V R) :
    ∃ L : ℝ, Tendsto h atTop (𝓝 L) := by
  refine tendsto_of_center_tracking hVtend ?_ htrack hrank
  exact Summable.of_nonneg_of_le (fun R => abs_nonneg _) hlink hVsum

end AnalyticCombinatorics.Ch8.Partitions.Erdos
