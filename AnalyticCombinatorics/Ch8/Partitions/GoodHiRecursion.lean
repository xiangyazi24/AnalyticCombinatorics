import AnalyticCombinatorics.Ch8.Partitions.ITERCoupling

/-!
# R7 Fact B via Doeblin: minorization on a sub-predicate ⟹ umass recursion

For the KILLED chain, the Doeblin minorization `δ ≤ cmass` holds only on the *active high-rank* window
`GoodHi` (where `Pker_window_minor`/brick 79 applies), NOT on absorbed/low-rank pairs.  This brick
generalizes the per-step contraction to any sub-predicate `Good` on which the minorization holds:

  `umass (t+1) ≤ umass t − δ · (Good-window mass of Umat t)`.

It follows from `umass_succ_eq` (`umass(t+1) = umass(t) − ∑ Umat·cmass`) since the coalescence mass
`∑ Umat·cmass ≥ δ · ∑_{Good} Umat`.  Then the (banked) CoalesceBridge consumes this with `g = ĝ` the
conditioned `Good`-fraction.  Deterministic finite-sum.  Opus-authored.
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (P : α → α → ℝ) (rnk : α → ℕ) (W : ℕ)
variable (hPnn : ∀ x y, 0 ≤ P x y) (hPmass : ∀ x, ∑ y, P x y = 1)
variable (i j : α)

include hPnn hPmass in
/-- **Minorization-on-`Good` ⟹ per-step umass contraction.** -/
theorem umass_succ_le_of_good (Good : α → α → Prop) [DecidableRel Good] (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hminor_good : ∀ x y, Good x y → δ ≤ cmass P rnk W x y) (t : ℕ) :
    umass P rnk W i j (t + 1)
      ≤ umass P rnk W i j t
        - δ * ∑ x, ∑ y, (if Good x y then Umat P rnk W i j t x y else 0) := by
  rw [umass_succ_eq P rnk W hPnn hPmass i j t]
  have hge : δ * ∑ x, ∑ y, (if Good x y then Umat P rnk W i j t x y else 0)
      ≤ ∑ x, ∑ y, Umat P rnk W i j t x y * cmass P rnk W x y := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun x _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun y _ => ?_)
    by_cases hg : Good x y
    · rw [if_pos hg, mul_comm]
      exact mul_le_mul_of_nonneg_left (hminor_good x y hg) (Umat_nonneg P rnk W hPnn hPmass i j t x y)
    · rw [if_neg hg, mul_zero]
      exact mul_nonneg (Umat_nonneg P rnk W hPnn hPmass i j t x y) (cmass_nonneg P rnk W hPnn x y)
  linarith

end AnalyticCombinatorics.Ch8.Partitions.Erdos
