import AnalyticCombinatorics.Ch8.Partitions.FKHittingBridge
import AnalyticCombinatorics.Ch8.Partitions.FKPartitionBridge

/-!
# Partition FK hitting bridge

This file packages the concrete drop-set interface for the partition residual
coupling: a uniform free-`KhatRes` hitting lower bound for
`{xy | δ ≤ cmass xy}` implies `umass → 0`.
-/

noncomputable section

open Filter Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (P : α → α → ℝ) (rnk : α → ℕ) (W : ℕ)

/-- The FK drop set where one departure survival factor is at most `1 - δ`. -/
def dropSet (δ : ℝ) (xy : α × α) : Prop :=
  δ ≤ cmass P rnk W xy.1 xy.2

noncomputable instance dropSet_decidable (δ : ℝ) : DecidablePred (dropSet P rnk W δ) :=
  Classical.decPred _

variable (hPnn : ∀ x y, 0 ≤ P x y) (hPmass : ∀ x, ∑ y, P x y = 1)

omit [DecidableEq α] in
lemma survivalWeight_le_of_dropSet (δ : ℝ) (xy : α × α)
    (hxy : dropSet P rnk W δ xy) :
    survivalWeight P rnk W xy ≤ 1 - δ := by
  dsimp [survivalWeight, dropSet] at hxy ⊢
  linarith

include hPnn hPmass in
/-- A uniform `KhatRes` hitting lower bound for the concrete drop set implies `umass → 0`. -/
theorem umass_tendsto_zero_of_uniform_drop_hit (i j : α)
    (δ p0 : ℝ) (hδ : 0 < δ) (hp0 : 0 < p0)
    (M : ℕ) (hM : 0 < M)
    (hhit :
      ∀ xy, p0 ≤ hitProb (KhatResPair P rnk W) (dropSet P rnk W δ) M xy) :
    Tendsto (fun t => umass P rnk W i j t) atTop (𝓝 0) := by
  classical
  have hc0 : 0 < δ * p0 := mul_pos hδ hp0
  have hdrop :
      ∀ xy, blockWeight
        (weightedKernel (KhatResPair P rnk W) (survivalWeight P rnk W)) M xy
          ≤ 1 - δ * p0 :=
    blockWeight_le_of_hitProb
      (Q := KhatResPair P rnk W)
      (w := survivalWeight P rnk W)
      (A := dropSet P rnk W δ)
      (δ := δ) (p0 := p0)
      (hQnn := KhatResPair_nonneg P rnk W hPnn hPmass)
      (hQsum := KhatResPair_sum P rnk W hPnn hPmass)
      (hw01 := survivalWeight_01 P rnk W hPnn hPmass)
      (hδ0 := hδ.le)
      (hdrop_on_A := survivalWeight_le_of_dropSet P rnk W δ)
      (M := M) hhit
  exact umass_tendsto_zero_of_fk_block_drop P rnk W hPnn hPmass i j M hM (δ * p0) hc0 hdrop

#print axioms umass_tendsto_zero_of_uniform_drop_hit

end AnalyticCombinatorics.Ch8.Partitions.Erdos
