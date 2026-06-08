import AnalyticCombinatorics.Ch8.Partitions.OverlapL1
import AnalyticCombinatorics.Ch8.Partitions.ITERCoupling

/-!
# R7 Fact B via Doeblin: harmonic values are controlled by overlap (route-independent bridge)

The convergence engine consumes a *minorization-driven* lower bound on the `m`-step overlap of two
killed-chain laws (produced by the windowed-coupling ITER).  This file supplies the missing half: a
bounded `m`-step-harmonic function `h` has its values at two starts pinned together by that overlap,
`|h i − h j| ≤ 2·B·(1 − overlap(pᵢ, pⱼ))`, where `pᵢ, pⱼ` are the two `m`-step laws.  This is pure
finite linear algebra (`∑(p−q)h ≤ B·‖p−q‖₁` plus the banked overlap/L¹ identity) and holds for *any*
convergence route — coupling, recurrence, or a direct renewal argument — so it can be banked now,
independent of how the overlap → 1 lower bound is eventually obtained.  Opus-authored.
-/

noncomputable section

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

open Finset

variable {α : Type*} [Fintype α]

/-- **L¹ control of a weighted difference.** For probability vectors `p, q` on a finite type and a
bounded weight `h` (`|h z| ≤ B`), the difference of the two `h`-averages is bounded by `B` times the
`L¹` distance `∑ |p − q|`. -/
lemma weighted_diff_le_L1 {p q h : α → ℝ} {B : ℝ}
    (hB : ∀ z, |h z| ≤ B) :
    |∑ z, p z * h z - ∑ z, q z * h z| ≤ B * ∑ z, |p z - q z| := by
  have hrw : ∑ z, p z * h z - ∑ z, q z * h z = ∑ z, (p z - q z) * h z := by
    rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl (fun z _ => ?_); ring
  rw [hrw]
  calc |∑ z, (p z - q z) * h z|
      ≤ ∑ z, |(p z - q z) * h z| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ z, |p z - q z| * |h z| := by
        refine Finset.sum_congr rfl (fun z _ => ?_); rw [abs_mul]
    _ ≤ ∑ z, |p z - q z| * B := by
        refine Finset.sum_le_sum (fun z _ => ?_)
        exact mul_le_mul_of_nonneg_left (hB z) (abs_nonneg _)
    _ = B * ∑ z, |p z - q z| := by rw [← Finset.sum_mul, mul_comm]

/-- **Harmonic values pinned by overlap.** If `h` is bounded by `B` and equals its average against
two probability vectors `p, q` (the two `m`-step killed-chain laws from starts `i, j`), then the two
harmonic values differ by at most `2·B·(1 − overlap p q)`.  As the windowed coupling drives
`overlap p q → 1`, the harmonic values coalesce. -/
theorem harmonic_diff_le_overlap {p q h : α → ℝ} {hi hj B : ℝ}
    (hp : ∑ z, p z = 1) (hq : ∑ z, q z = 1)
    (hB : ∀ z, |h z| ≤ B)
    (hhi : hi = ∑ z, p z * h z) (hhj : hj = ∑ z, q z * h z) :
    |hi - hj| ≤ 2 * B * (1 - overlap p q) := by
  have hL1 : ∑ z, |p z - q z| = 2 * (1 - overlap p q) := by
    have hmin : ∀ z, min (p z) (q z) = (p z + q z - |p z - q z|) / 2 := by
      intro z
      rcases le_total (p z) (q z) with hle | hle
      · rw [min_eq_left hle, abs_of_nonpos (by linarith)]; ring
      · rw [min_eq_right hle, abs_of_nonneg (by linarith)]; ring
    have hov : overlap p q = 1 - (1 / 2) * ∑ z, |p z - q z| := by
      unfold overlap
      rw [Finset.sum_congr rfl (fun z _ => hmin z), ← Finset.sum_div, Finset.sum_sub_distrib,
        Finset.sum_add_distrib, hp, hq]
      ring
    rw [hov]; ring
  rw [hhi, hhj]
  calc |∑ z, p z * h z - ∑ z, q z * h z|
      ≤ B * ∑ z, |p z - q z| := weighted_diff_le_L1 hB
    _ = B * (2 * (1 - overlap p q)) := by rw [hL1]
    _ = 2 * B * (1 - overlap p q) := by ring

end AnalyticCombinatorics.Ch8.Partitions.Erdos
