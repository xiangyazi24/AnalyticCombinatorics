import AnalyticCombinatorics.Ch8.Partitions.RankBandEntrance
import AnalyticCombinatorics.Ch8.Partitions.CeilingHit

/-!
# TASK T2-ceiling, L4 core helper: the one-step entrance lower bound

For the same-ceiling value Doeblin (L4), the entrance laws from two ceiling-level values `x, y`
(`rnk x = rnk y = C`) into the band `B = ceilBand R (A R) = {rnk < C}` are compared on the in-band
slice.  The basic reduction is that the first-entrance kernel dominates the **one-step** kernel on
any in-band target `z ∈ B`:

  `Pker x z ≤ enterBandKer Pker B x z`   (for `x ∉ B`, `z ∈ B`).

(The first entrance can land at `z` directly on its first step; the remaining paths only add
nonnegative mass.)  Consequently

  `∑_{z ∈ slice} min (Pker x z) (Pker y z)
      ≤ ∑_{z ∈ slice} min (enterBandKer Pker B x z) (enterBandKer Pker B y z)`,

so a value-level overlap of the *one-step* predecessor laws on the slice transfers to the
first-entrance laws.  This file proves these two reductions; the residual analytic content of L4 is
the positive one-step value overlap `∑_{z ∈ slice} min (Pker x z) (Pker y z) ≥ β`, a two-start
value-window estimate.

NEW file; imports the banked entrance kernel and ceiling-hit cores, does not modify them.
Opus-authored.
-/

noncomputable section

open Filter Topology BigOperators

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- **One-step entrance lower bound.**  If the start `x` is off the band (`x ∉ B`) and the target
`z` is in the band (`z ∈ B`) with `z < x`, then the first-entrance kernel dominates one `Pker` step:
`Pker x z ≤ enterBandKer Pker B x z`.  (The `k = z` term of the entrance recursion gives
`Pker x z · enterBandKer Pker B z z = Pker x z · 1 = Pker x z`; the rest is nonnegative.) -/
lemma Pker_le_enterBandKer {B : Finset ℕ} {x z : ℕ}
    (hxB : x ∉ B) (hzB : z ∈ B) (hzx : z < x) :
    Pker x z ≤ enterBandKer Pker B x z := by
  classical
  rw [enterBandKer_eq, if_neg hxB]
  -- isolate the k = z term
  have hzrange : z ∈ Finset.range x := Finset.mem_range.mpr hzx
  have hzz : enterBandKer Pker B z z = 1 := by
    rw [enterBandKer_eq, if_pos hzB, if_pos rfl]
  have hterm : Pker x z = Pker x z * enterBandKer Pker B z z := by rw [hzz, mul_one]
  rw [hterm]
  refine Finset.single_le_sum (f := fun k => Pker x k * enterBandKer Pker B k z) ?_ hzrange
  intro k _
  exact mul_nonneg (Pker_nonneg x k) (enterBandKer_nonneg (fun a b => Pker_nonneg a b) k z)

/-- **Slice overlap transfer.**  Over any `slice` of in-band targets (each `z ∈ slice` with `z ∈ B`
and `z < x`, `z < y`), the one-step predecessor-law overlap is dominated by the first-entrance-law
overlap.  Reduces the value-level Doeblin (L4) to a positive overlap of the one-step laws
`Pker x ·`, `Pker y ·`. -/
lemma min_Pker_le_min_enterBandKer_sum {B slice : Finset ℕ} {x y : ℕ}
    (hxB : x ∉ B) (hyB : y ∉ B)
    (hslice : ∀ z ∈ slice, z ∈ B ∧ z < x ∧ z < y) :
    ∑ z ∈ slice, min (Pker x z) (Pker y z)
      ≤ ∑ z ∈ slice, min (enterBandKer Pker B x z) (enterBandKer Pker B y z) := by
  refine Finset.sum_le_sum (fun z hz => ?_)
  obtain ⟨hzB, hzx, hzy⟩ := hslice z hz
  exact min_le_min (Pker_le_enterBandKer hxB hzB hzx) (Pker_le_enterBandKer hyB hzB hzy)

#print axioms Pker_le_enterBandKer
#print axioms min_Pker_le_min_enterBandKer_sum

end AnalyticCombinatorics.Ch8.Partitions.Erdos
