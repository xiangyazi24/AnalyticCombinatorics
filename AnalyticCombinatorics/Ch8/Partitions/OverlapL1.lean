import Mathlib

/-!
# R7 Fact B via Doeblin: overlap = 1 − ½·L¹-distance

The bridge from kernel L¹-continuity to the windowed minorization `(B_W)`.  For two probability vectors
`p, q` on a finite set, `∑ min(p,q) = 1 − ½·∑|p − q|`.  So an `L¹` bound `∑|p − q| ≤ 2(1−δ)` yields the
overlap bound `∑ min(p,q) ≥ δ` — exactly the comparable-rank minorization the ITER consumes.  The hard
analytic content (`Pker` L¹-continuity in the start index) then reduces to bounding `∑|Pker x − Pker y|`.
Opus-authored.
-/

noncomputable section

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- For probability vectors, total overlap equals `1` minus half the `L¹` distance. -/
lemma overlap_eq_one_sub_half_L1 {s : Finset ℕ} {p q : ℕ → ℝ}
    (hp : ∑ k ∈ s, p k = 1) (hq : ∑ k ∈ s, q k = 1) :
    ∑ k ∈ s, min (p k) (q k) = 1 - (1 / 2) * ∑ k ∈ s, |p k - q k| := by
  have hmin : ∀ k ∈ s, min (p k) (q k) = (p k + q k - |p k - q k|) / 2 := by
    intro k _
    rcases le_total (p k) (q k) with h | h
    · rw [min_eq_left h, abs_of_nonpos (by linarith)]; ring
    · rw [min_eq_right h, abs_of_nonneg (by linarith)]; ring
  rw [Finset.sum_congr rfl hmin, ← Finset.sum_div, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, hp, hq]
  ring

/-- An `L¹` bound gives a minorization (overlap lower bound). -/
lemma overlap_ge_of_L1_le {s : Finset ℕ} {p q : ℕ → ℝ} {δ : ℝ}
    (hp : ∑ k ∈ s, p k = 1) (hq : ∑ k ∈ s, q k = 1)
    (hL1 : ∑ k ∈ s, |p k - q k| ≤ 2 * (1 - δ)) :
    δ ≤ ∑ k ∈ s, min (p k) (q k) := by
  rw [overlap_eq_one_sub_half_L1 hp hq]
  linarith

end AnalyticCombinatorics.Ch8.Partitions.Erdos
