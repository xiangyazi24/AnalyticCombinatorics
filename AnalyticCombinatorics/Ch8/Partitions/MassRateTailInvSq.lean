import Mathlib

/-!
# Mass-rate campaign: shifted Basel tail `Σ' 1/(i+N+1)² ≤ 2/(N+1)`

The polynomial-tail input for the weighted-decay keystone, via `sum_Ioo_inv_sq_le`.
Opus-authored.
-/

set_option maxHeartbeats 800000

noncomputable section

open Finset
open scoped BigOperators

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- Basel tail (shifted form): `Σ'_{i} 1/(i+N+1)² ≤ 2/(N+1)`. -/
lemma tail_inv_sq_shift (N : ℕ) :
    (∑' i : ℕ, 1 / (((i + N + 1 : ℕ)) : ℝ) ^ 2) ≤ 2 / ((N : ℝ) + 1) := by
  apply Real.tsum_le_of_sum_range_le (fun i => by positivity)
  intro n
  have hreindex : (∑ i ∈ Finset.range n, 1 / (((i + N + 1 : ℕ)) : ℝ) ^ 2)
      = ∑ k ∈ Finset.Ico (N + 1) (N + 1 + n), 1 / ((k : ℝ)) ^ 2 := by
    rw [Finset.sum_Ico_eq_sum_range]
    have hsub : N + 1 + n - (N + 1) = n := by omega
    rw [hsub]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [show i + N + 1 = N + 1 + i from by omega]
  rw [hreindex]
  have hIco : Finset.Ico (N + 1) (N + 1 + n) = Finset.Ioo N (N + 1 + n) := by
    ext x
    simp only [Finset.mem_Ico, Finset.mem_Ioo]
    omega
  rw [hIco]
  have hbound := sum_Ioo_inv_sq_le (α := ℝ) N (N + 1 + n)
  simp only [one_div]
  exact hbound

end AnalyticCombinatorics.Ch8.Partitions.Erdos
