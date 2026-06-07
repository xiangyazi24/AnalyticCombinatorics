import AnalyticCombinatorics.Ch8.Partitions.PartitionRenewal

/-!
# R7 Fact B via Doeblin: boundedness of `hitVal` and substochasticity of `Pker`

The hitting value `hitVal P rank J φ` is a sub-convex combination of boundary values of `φ`, so it
inherits `φ`'s bound: if `φ` is globally bounded by `Mφ`, `P` is nonnegative and substochastic above the
cutoff, then `|hitVal P rank J φ n| ≤ Mφ` for all `n` (strong induction on the predecessor recursion).
The concrete predecessor kernel `Pker` is substochastic (`∑_{k<n} Pker n k ≤ 1`): the row mass is `1`
when `kernelMass n ≠ 0` and `0` otherwise.  Opus-authored.
-/

noncomputable section

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- `Pker` is substochastic: each row sums to at most `1`. -/
lemma Pker_sum_le_one (n : ℕ) : ∑ k ∈ Finset.range n, Pker n k ≤ 1 := by
  by_cases hn : 2 ≤ n
  · by_cases hkm : kernelMass n = 0
    · have hz : ∀ k ∈ Finset.range n, Pker n k = 0 := by
        intro k _; unfold Pker; split
        · rw [hkm, div_zero]
        · rfl
      rw [Finset.sum_congr rfl hz, Finset.sum_const_zero]; norm_num
    · exact le_of_eq (Pker_mass hn hkm)
  · have hz : ∀ k ∈ Finset.range n, Pker n k = 0 := by
      intro k hk; rw [Finset.mem_range] at hk; unfold Pker; rw [if_neg (by omega)]
    rw [Finset.sum_congr rfl hz, Finset.sum_const_zero]; norm_num

variable {P : ℕ → ℕ → ℝ} {rank : ℕ → ℕ} {J : ℕ} {φ : ℕ → ℝ}

/-- A globally bounded boundary `φ` makes the hitting value bounded by the same constant. -/
lemma hitVal_abs_le {Mφ : ℝ} (hMφ0 : 0 ≤ Mφ) (hφ : ∀ m, |φ m| ≤ Mφ)
    (hPnn : ∀ n k, 0 ≤ P n k)
    (hsub : ∀ n, J ≤ rank n → ∑ k ∈ Finset.range n, P n k ≤ 1) :
    ∀ n, |hitVal P rank J φ n| ≤ Mφ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [hitVal_eq]
    by_cases hb : rank n < J
    · rw [if_pos hb]; exact hφ n
    · rw [if_neg hb]
      have hJ : J ≤ rank n := not_lt.mp hb
      calc |∑ k ∈ Finset.range n, P n k * hitVal P rank J φ k|
          ≤ ∑ k ∈ Finset.range n, |P n k * hitVal P rank J φ k| :=
            Finset.abs_sum_le_sum_abs _ _
        _ = ∑ k ∈ Finset.range n, P n k * |hitVal P rank J φ k| := by
            apply Finset.sum_congr rfl; intro k _
            rw [abs_mul, abs_of_nonneg (hPnn n k)]
        _ ≤ ∑ k ∈ Finset.range n, P n k * Mφ := by
            apply Finset.sum_le_sum; intro k hk
            rw [Finset.mem_range] at hk
            exact mul_le_mul_of_nonneg_left (ih k hk) (hPnn n k)
        _ = (∑ k ∈ Finset.range n, P n k) * Mφ := by rw [Finset.sum_mul]
        _ ≤ 1 * Mφ := mul_le_mul_of_nonneg_right (hsub n hJ) hMφ0
        _ = Mφ := one_mul _

end AnalyticCombinatorics.Ch8.Partitions.Erdos
