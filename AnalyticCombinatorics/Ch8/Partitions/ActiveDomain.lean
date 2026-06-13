import AnalyticCombinatorics.Ch8.Partitions.KhatRes

/-!
# Active / frozen split for the killed pair coupling (TASK #9 layer A)

The all-start FK drop hypothesis is false for the killed partition chain because *frozen-apart*
below-cutoff pairs `(x,y)` with `x ≠ y` are absorbed point masses with zero common mass: the free
residual walk stays put, `cmass = 0`, and no drop set is ever hit.  This file isolates exactly those
rows.

We work with a finite state type `α`, a rank `rnk`, a window `W`, and a kernel `P` that is
*point-frozen below the cutoff* `J`: rows `x` with `rnk x < J` are the absorbing point mass at `x`
(`P x z = if z = x then 1 else 0`).  This is precisely the structure of `killedKer` on the finite
segment.  We define

  `Active J xy := J ≤ rnk xy.1 ∧ J ≤ rnk xy.2`

and prove that a frozen-apart counter-row (`rnk x < J`, `rnk y < J`, `x ≠ y`) is `¬ Active` and has
`cmass P rnk W x y = 0`.  Opus-authored.
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (P : α → α → ℝ) (rnk : α → ℕ) (W J : ℕ)

/-- The active domain for the killed coupling at cutoff `J`: both ranks are at the cutoff or above. -/
def Active (xy : α × α) : Prop := J ≤ rnk xy.1 ∧ J ≤ rnk xy.2

instance Active_decidable : DecidablePred (Active rnk J : α × α → Prop) := by
  intro xy; unfold Active; infer_instance

/-- A kernel is *point-frozen below `J`*: each below-cutoff row is the absorbing point mass. -/
def PointFrozenBelow : Prop :=
  ∀ x z, rnk x < J → P x z = (if z = x then 1 else 0)

variable {P rnk W J}

/-- A frozen-apart counter-row (both ranks below `J`, distinct points) is not in the active domain. -/
lemma not_active_of_below {x y : α} (hx : rnk x < J) :
    ¬ Active rnk J (x, y) := by
  intro h
  exact absurd h.1 (by simpa using Nat.not_le.mpr hx)

/-- **Frozen-apart counter-rows have zero common mass.**  If `P` is point-frozen below the cutoff and
`(x, y)` are two distinct below-cutoff states, the two rows are different point masses, so their
windowed overlap `cmass` is `0`. -/
lemma cmass_eq_zero_of_frozen_apart
    (hfrozen : PointFrozenBelow P rnk J)
    {x y : α} (hx : rnk x < J) (hy : rnk y < J) (hxy : x ≠ y) :
    cmass P rnk W x y = 0 := by
  unfold cmass
  apply Finset.sum_eq_zero
  intro z _
  unfold Cpart
  by_cases hg : GoodW rnk W x y
  · rw [if_pos hg]
    rw [hfrozen x z hx, hfrozen y z hy]
    -- min of two point masses at distinct points is 0
    have hax : (0:ℝ) ≤ (if z = x then (1:ℝ) else 0) := by split <;> norm_num
    have hay : (0:ℝ) ≤ (if z = y then (1:ℝ) else 0) := by split <;> norm_num
    by_cases hzx : z = x
    · subst hzx
      rw [if_pos rfl, if_neg hxy]
      norm_num
    · rw [if_neg hzx]
      exact min_eq_left hay
  · rw [if_neg hg]

/-- The frozen-apart counter-rows together: `¬ Active` and `cmass = 0`. -/
lemma frozen_apart_not_active_cmass_zero
    (hfrozen : PointFrozenBelow P rnk J)
    {x y : α} (hx : rnk x < J) (hy : rnk y < J) (hxy : x ≠ y) :
    ¬ Active rnk J (x, y) ∧ cmass P rnk W x y = 0 :=
  ⟨not_active_of_below hx, cmass_eq_zero_of_frozen_apart hfrozen hx hy hxy⟩

#print axioms cmass_eq_zero_of_frozen_apart
#print axioms frozen_apart_not_active_cmass_zero

end AnalyticCombinatorics.Ch8.Partitions.Erdos
