import AnalyticCombinatorics.Ch8.Partitions.PartitionRenewal

/-!
# R7 Fact B via Doeblin: concrete facts about `rnk` and `kernelMass`

Two elementary facts needed to instantiate the abstract `tendsto_of_killed_doeblin` for the concrete
Erdős predecessor kernel: the rank map `rnk n = ⌊3√n⌋` diverges (`rnk → atTop`), and the kernel mass
`kernelMass n` is eventually strictly positive (it dominates the window mass, which is `≥ ν > 0`
eventually).  The latter makes `Pker` row-stochastic for large `n` (via `Pker_mass`).  Opus-authored.
-/

noncomputable section

open Filter Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- The rank map diverges: `rnk n = ⌊3√n⌋ → ∞`. -/
lemma rnk_tendsto_atTop : Tendsto rnk atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  refine ⟨(b + 1) ^ 2, fun n hn => ?_⟩
  have h1 : ((b + 1) ^ 2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hb_le_sqrt : (b : ℝ) ≤ Real.sqrt (n : ℝ) := by
    rw [show (b : ℝ) = Real.sqrt ((b : ℝ) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    apply Real.sqrt_le_sqrt
    nlinarith [h1, (Nat.cast_nonneg b : (0:ℝ) ≤ (b:ℝ))]
  have hsqrt : (b : ℝ) ≤ 3 * Real.sqrt (n : ℝ) := by
    have := Real.sqrt_nonneg (n : ℝ); linarith
  unfold rnk
  exact Nat.le_floor hsqrt

/-- The kernel mass is eventually strictly positive (it dominates the positive window mass). -/
lemma kernelMass_pos_eventually : ∀ᶠ n : ℕ in atTop, 0 < kernelMass n := by
  obtain ⟨ν, hν, hwin⟩ := kernelWindow_one_two_pos
  filter_upwards [hwin] with n hn
  have hle : kernelWindow 1 2 n ≤ kernelMass n := by
    unfold kernelWindow kernelMass
    apply Finset.sum_le_sum
    intro m hm
    split
    · exact le_refl _
    · exact erdosWeight_nonneg_of_mem hm
  linarith

end AnalyticCombinatorics.Ch8.Partitions.Erdos
