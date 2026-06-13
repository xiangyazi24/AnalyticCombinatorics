import AnalyticCombinatorics.Ch8.Partitions.FKBlockBridge
import AnalyticCombinatorics.Ch8.Partitions.KhatRes

/-!
# Feynman--Kac bridge for the partition residual coupling

This file instantiates the abstract finite-state FK block bridge for the
partition residual coupling.  The residual kernel factors as the stochastic
conditioned residual kernel `KhatResPair` times the departure survival weight
`1 - cmass`; consequently `umass` is exactly the total mass of the associated
FK semigroup.
-/

noncomputable section

open Filter Finset Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (P : α → α → ℝ) (rnk : α → ℕ) (W : ℕ)

/-- The residual product coupling kernel as a kernel on pair states. -/
def KresPair (xy zw : α × α) : ℝ :=
  Kres P rnk W xy.1 xy.2 zw.1 zw.2

/-- FK survival weight for a departure pair. -/
def survivalWeight (xy : α × α) : ℝ :=
  1 - cmass P rnk W xy.1 xy.2

variable (hPnn : ∀ x y, 0 ≤ P x y) (hPmass : ∀ x, ∑ y, P x y = 1)

include hPnn hPmass in
lemma Kres_factor_KhatRes (x y a b : α) :
    Kres P rnk W x y a b =
      (1 - cmass P rnk W x y) * KhatRes P rnk W x y a b := by
  by_cases h : cmass P rnk W x y < 1
  · have hden : 1 - cmass P rnk W x y ≠ 0 := by linarith
    unfold KhatRes
    simp only [if_pos h]
    field_simp [hden]
  · have hc1 : cmass P rnk W x y = 1 :=
      le_antisymm (cmass_le_one P rnk W hPnn hPmass x y) (not_lt.mp h)
    unfold Kres KhatRes
    simp [hc1]

include hPnn hPmass in
lemma KresPair_eq_weightedKernel :
    KresPair P rnk W =
      weightedKernel (KhatResPair P rnk W) (survivalWeight P rnk W) := by
  funext xy zw
  cases xy with
  | mk x y =>
      cases zw with
      | mk a b =>
          simp [KresPair, weightedKernel, KhatResPair, survivalWeight,
            Kres_factor_KhatRes P rnk W hPnn hPmass x y a b]

omit [DecidableEq α] in
include hPnn hPmass in
lemma survivalWeight_01 (xy : α × α) :
    0 ≤ survivalWeight P rnk W xy ∧ survivalWeight P rnk W xy ≤ 1 := by
  classical
  cases xy with
  | mk x y =>
      constructor
      · dsimp [survivalWeight]
        linarith [cmass_le_one P rnk W hPnn hPmass x y]
      · dsimp [survivalWeight]
        linarith [cmass_nonneg P rnk W hPnn x y]

lemma evolve_KresPair_pairDelta_eq_Umat (i j : α) :
    ∀ t xy,
      evolve (KresPair P rnk W) (pairDelta i j) t xy =
        Umat P rnk W i j t xy.1 xy.2 := by
  intro t
  induction t with
  | zero =>
      intro xy
      cases xy with
      | mk a b =>
          simp [evolve, pairDelta, Umat, Prod.ext_iff]
  | succ t ih =>
      intro xy
      cases xy with
      | mk a b =>
          simp only [evolve, Umat]
          rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl ?_
          intro x _hx
          refine Finset.sum_congr rfl ?_
          intro y _hy
          rw [ih (x, y)]
          rfl

lemma umass_eq_uMass_KresPair (i j : α) (t : ℕ) :
    umass P rnk W i j t =
      uMass (KresPair P rnk W) (pairDelta i j) t := by
  unfold umass uMass
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl ?_
  intro x _hx
  refine Finset.sum_congr rfl ?_
  intro y _hy
  rw [evolve_KresPair_pairDelta_eq_Umat P rnk W i j t (x, y)]

include hPnn hPmass in
/-- `umass` tends to zero from a uniform FK block drop for the concrete residual walk. -/
theorem umass_tendsto_zero_of_fk_block_drop (i j : α)
    (M : ℕ) (hM : 0 < M) (c0 : ℝ) (hc0 : 0 < c0)
    (hdrop :
      ∀ xy, blockWeight
        (weightedKernel (KhatResPair P rnk W) (survivalWeight P rnk W)) M xy ≤ 1 - c0) :
    Tendsto (fun t => umass P rnk W i j t) atTop (𝓝 0) := by
  have hfk := fk_block_bridge
    (Q := KhatResPair P rnk W)
    (w := survivalWeight P rnk W)
    (hQnn := KhatResPair_nonneg P rnk W hPnn hPmass)
    (hQsum := KhatResPair_sum P rnk W hPnn hPmass)
    (hw01 := survivalWeight_01 P rnk W hPnn hPmass)
    (M := M) (hM := hM) (c0 := c0) (hc0 := hc0)
    (hdrop := hdrop)
    (μ0 := pairDelta i j)
    (hμ0nn := pairDelta_nonneg i j)
    (hμ0sum := pairDelta_sum i j)
  refine hfk.congr' ?_
  exact Eventually.of_forall fun t => by
    rw [← KresPair_eq_weightedKernel P rnk W hPnn hPmass]
    change uMass (KresPair P rnk W) (pairDelta i j) t = umass P rnk W i j t
    exact (umass_eq_uMass_KresPair P rnk W i j t).symm

#print axioms Kres_factor_KhatRes
#print axioms KresPair_eq_weightedKernel
#print axioms umass_eq_uMass_KresPair
#print axioms umass_tendsto_zero_of_fk_block_drop

end AnalyticCombinatorics.Ch8.Partitions.Erdos
