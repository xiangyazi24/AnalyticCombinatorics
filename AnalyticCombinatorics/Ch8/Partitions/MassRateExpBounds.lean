import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.MassRateMoments

/-!
# Mass-rate campaign: polynomial exponential bounds (R10 bricks 1–3)

Two-sided polynomial bounds for `e^x − 1` on `[0,1]` from `Real.exp_bound` at orders 3, 4 —
the only exp-Taylor input the whole moment package needs.  Opus-authored.
-/

set_option maxHeartbeats 400000

noncomputable section

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- Order-3 remainder: `|e^x − 1 − x − x²/2| ≤ x³` on `[0,1]`. -/
lemma exp_sub_one_sub_self_sq_bound {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |Real.exp x - 1 - x - x ^ 2 / 2| ≤ x ^ 3 := by
  have habs : |x| ≤ 1 := by
    rw [abs_of_nonneg hx0]
    exact hx1
  have h := Real.exp_bound habs (n := 3) (by norm_num)
  have hsum : ∑ i ∈ Finset.range 3, x ^ i / (Nat.factorial i : ℝ)
      = 1 + x + x ^ 2 / 2 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero]
    norm_num [Nat.factorial]
  rw [hsum] at h
  have habs3 : |x| ^ 3 = x ^ 3 := by
    rw [abs_of_nonneg hx0]
  rw [habs3] at h
  calc |Real.exp x - 1 - x - x ^ 2 / 2|
      = |Real.exp x - (1 + x + x ^ 2 / 2)| := by ring_nf
    _ ≤ x ^ 3 * ((3 : ℕ).succ / ((Nat.factorial 3 : ℝ) * 3)) := h
    _ ≤ x ^ 3 := by
        have hx3 : (0 : ℝ) ≤ x ^ 3 := by positivity
        have hc : ((3 : ℕ).succ : ℝ) / ((Nat.factorial 3 : ℝ) * 3) ≤ 1 := by
          norm_num [Nat.factorial]
        nlinarith [hx3, hc]

/-- Two-sided order-3 bounds: `x + x²/2 ≤ e^x − 1 ≤ x + x²/2 + x³` on `[0,1]`. -/
lemma exp_sub_one_bounds_order3 {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x + x ^ 2 / 2 ≤ Real.exp x - 1 ∧ Real.exp x - 1 ≤ x + x ^ 2 / 2 + x ^ 3 := by
  have h := exp_sub_one_sub_self_sq_bound hx0 hx1
  have h1 := (abs_le.mp h).1
  have h2 := (abs_le.mp h).2
  constructor
  · -- the lower side needs the sharper fact: e^x ≥ 1 + x + x²/2 for x ≥ 0 (all-order lower)
    -- from |R₃| ≤ x³ alone we get e^x − 1 ≥ x + x²/2 − x³; sharpen via sum_le_exp:
    have hsum := Real.sum_le_exp_of_nonneg hx0 3
    have hsum' : 1 + x + x ^ 2 / 2 ≤ Real.exp x := by
      have heq : ∑ i ∈ Finset.range 3, x ^ i / (Nat.factorial i : ℝ)
          = 1 + x + x ^ 2 / 2 := by
        rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
          Finset.sum_range_zero]
        norm_num [Nat.factorial]
      rw [heq] at hsum
      exact hsum
    linarith
  · linarith

/-- Order-4 remainder: `|e^x − 1 − x − x²/2 − x³/6| ≤ x⁴` on `[0,1]`. -/
lemma exp_sub_one_order4_bound {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |Real.exp x - 1 - x - x ^ 2 / 2 - x ^ 3 / 6| ≤ x ^ 4 := by
  have habs : |x| ≤ 1 := by
    rw [abs_of_nonneg hx0]
    exact hx1
  have h := Real.exp_bound habs (n := 4) (by norm_num)
  have hsum : ∑ i ∈ Finset.range 4, x ^ i / (Nat.factorial i : ℝ)
      = 1 + x + x ^ 2 / 2 + x ^ 3 / 6 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num [Nat.factorial]
  rw [hsum] at h
  have habs4 : |x| ^ 4 = x ^ 4 := by
    rw [abs_of_nonneg hx0]
  rw [habs4] at h
  calc |Real.exp x - 1 - x - x ^ 2 / 2 - x ^ 3 / 6|
      = |Real.exp x - (1 + x + x ^ 2 / 2 + x ^ 3 / 6)| := by ring_nf
    _ ≤ x ^ 4 * ((4 : ℕ).succ / ((Nat.factorial 4 : ℝ) * 4)) := h
    _ ≤ x ^ 4 := by
        have hx4 : (0 : ℝ) ≤ x ^ 4 := by positivity
        have hc : ((4 : ℕ).succ : ℝ) / ((Nat.factorial 4 : ℝ) * 4) ≤ 1 := by
          norm_num [Nat.factorial]
        nlinarith [hx4, hc]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
