import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.MassRateLambert

/-!
# Mass-rate campaign: the quadratic geometric sum (M₁-side ingredient)

`Σ'_{d≥1} d²·y^d = y(1+y)/(1−y)³` — from Mathlib's choose-geometric sums via
`n² = 2·C(n+2,2) − 3·C(n+1,1) + C(n,0)`.  Feeds the two-exponent Lambert
rearrangement for `M₁`.  Opus-authored.
-/

set_option maxHeartbeats 800000

noncomputable section

open Filter Finset
open scoped BigOperators Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- `Σ'_{n:ℕ} n²·yⁿ = y(1+y)/(1−y)³` for `‖y‖ < 1`. -/
lemma tsum_nat_sq_mul_geometric {y : ℝ} (hy : ‖y‖ < 1) :
    ∑' n : ℕ, ((n : ℝ)) ^ 2 * y ^ n = y * (1 + y) / (1 - y) ^ 3 := by
  have hy1 : (1 : ℝ) - y ≠ 0 := by
    intro h
    have : y = 1 := by linarith
    rw [this] at hy
    norm_num at hy
  have h0 : HasSum (fun n : ℕ => ((n + 0).choose 0 : ℝ) * y ^ n) (1 / (1 - y) ^ (0 + 1)) :=
    hasSum_choose_mul_geometric_of_norm_lt_one 0 hy
  have h1 : HasSum (fun n : ℕ => ((n + 1).choose 1 : ℝ) * y ^ n) (1 / (1 - y) ^ (1 + 1)) :=
    hasSum_choose_mul_geometric_of_norm_lt_one 1 hy
  have h2 : HasSum (fun n : ℕ => ((n + 2).choose 2 : ℝ) * y ^ n) (1 / (1 - y) ^ (2 + 1)) :=
    hasSum_choose_mul_geometric_of_norm_lt_one 2 hy
  have hcomb : HasSum (fun n : ℕ => ((n : ℝ)) ^ 2 * y ^ n)
      (2 * (1 / (1 - y) ^ 3) - 3 * (1 / (1 - y) ^ 2) + 1 / (1 - y) ^ 1) := by
    have hstep := ((h2.mul_left 2).sub (h1.mul_left 3)).add h0
    convert hstep using 1
    funext n
    have hc2 : ((n + 2).choose 2 : ℝ) = ((n : ℝ) + 2) * ((n : ℝ) + 1) / 2 := by
      rw [Nat.cast_choose_two]
      push_cast
      ring
    have hc1 : ((n + 1).choose 1 : ℝ) = (n : ℝ) + 1 := by
      rw [Nat.choose_one_right]
      push_cast
      ring
    have hc0 : ((n + 0).choose 0 : ℝ) = 1 := by
      rw [Nat.choose_zero_right]
      norm_num
    rw [hc2, hc1, hc0] at *
    ring
  rw [hcomb.tsum_eq]
  field_simp
  ring

/-- `Σ'_{d:ℕ+} d²·y^d = y(1+y)/(1−y)³` for `‖y‖ < 1`. -/
lemma tsum_pnat_sq_mul_geometric {y : ℝ} (hy : ‖y‖ < 1) :
    ∑' d : ℕ+, ((d : ℕ) : ℝ) ^ 2 * y ^ (d : ℕ) = y * (1 + y) / (1 - y) ^ 3 := by
  have hsum : Summable (fun n : ℕ => ((n : ℝ)) ^ 2 * y ^ n) := by
    have := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2 hy
    exact this
  have hbase := tsum_nat_sq_mul_geometric hy
  have hshift := tsum_pnat_eq_tsum_succ (f := fun n : ℕ => ((n : ℝ)) ^ 2 * y ^ n)
  rw [hshift]
  have hzero := hsum.tsum_eq_zero_add
  rw [← hbase, hzero]
  simp

end AnalyticCombinatorics.Ch8.Partitions.Erdos
