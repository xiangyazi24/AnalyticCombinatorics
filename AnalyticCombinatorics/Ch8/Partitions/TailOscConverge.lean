import Mathlib

/-!
# R7 Fact B via Doeblin: tail-oscillation → 0 ⟹ convergence

The final abstract closer of the §9 route.  If a sequence `h` has a *tail-oscillation* dominator `V`
— `|h i − h j| ≤ V R` whenever both `rank i, rank j ≥ R` — and `V → 0`, then `h` is Cauchy along the
filter `rank → atTop`, hence converges.  This is the kernel-free endgame: the Doeblin/escape analysis
only has to drive the single scalar sequence `V` to `0` (via `tendsto_zero_of_step_contraction`), and
this lemma turns that into `∃ L, h → L` — exactly Fact B for `hitVal`.  Opus-authored.
-/

noncomputable section

open Filter Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- **§9 endgame.** A vanishing tail-oscillation dominator `V` forces `h` to converge. -/
theorem tendsto_of_tail_osc_to_zero {h V : ℕ → ℝ} {rank : ℕ → ℕ}
    (hrank : Tendsto rank atTop atTop)
    (hVtend : Tendsto V atTop (𝓝 0))
    (hVosc : ∀ R i j, R ≤ rank i → R ≤ rank j → |h i - h j| ≤ V R) :
    ∃ L : ℝ, Tendsto h atTop (𝓝 L) := by
  have hcau : CauchySeq h := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    -- pick a rank cutoff `R` where the tail oscillation is `< ε`
    obtain ⟨R, hR0⟩ := Metric.tendsto_atTop.1 hVtend ε hε
    have hR := hR0 R le_rfl
    have hVR : V R < ε := by
      rw [Real.dist_eq, sub_zero] at hR
      exact lt_of_le_of_lt (le_abs_self _) hR
    -- past some index every term has rank `≥ R`
    obtain ⟨N, hN⟩ := (tendsto_atTop_atTop.1 hrank) R
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [Real.dist_eq]
    exact lt_of_le_of_lt (hVosc R m n (hN m hm) (hN n hn)) hVR
  exact cauchySeq_tendsto_of_complete hcau

end AnalyticCombinatorics.Ch8.Partitions.Erdos
