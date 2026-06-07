import AnalyticCombinatorics.Ch8.Partitions.KilledHarmonic

/-!
# R7 Fact B via Doeblin: the killed kernel and its powers are row-stochastic

To feed `KPowK L P̃` into the Doeblin escape contraction (`doeblin_average_diff_bound` /
`doeblin_escape_bound`, whose `p, q` must be probability vectors), we need each row of `P̃` and of every
power `KPowK L P̃` to sum to `1` over `range (n+1)`.  Given the base kernel `P` is row-stochastic over
`range n` (the predecessor mass is normalized) with predecessor support (`n ≤ k → P n k = 0`), the
killed kernel absorbs the missing diagonal mass below the cutoff, so `∑_{k ∈ range (n+1)} P̃ n k = 1`;
the powers then preserve this by induction (the inner row-sum truncates to `range (j+1)` via
`KPowK_support`).  Opus-authored.
-/

noncomputable section

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {P : ℕ → ℕ → ℝ} {rank : ℕ → ℕ} {J : ℕ}

/-- The killed kernel is row-stochastic over `range (n+1)`. -/
lemma killedKer_row_sum (hrow : ∀ n, ∑ k ∈ Finset.range n, P n k = 1)
    (hsupp : ∀ n k, n ≤ k → P n k = 0) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), killedKer P rank J n k = 1 := by
  unfold killedKer
  by_cases hb : rank n < J
  · simp only [if_pos hb]
    rw [Finset.sum_ite_eq' (Finset.range (n + 1)) n (fun _ => (1 : ℝ)),
      if_pos (Finset.self_mem_range_succ n)]
  · simp only [if_neg hb]
    rw [Finset.sum_range_succ, hsupp n n (le_refl n), add_zero, hrow n]

/-- Every killed power is row-stochastic over `range (n+1)`. -/
lemma KPowK_row_sum {Q : ℕ → ℕ → ℝ}
    (hQrow : ∀ m, ∑ k ∈ Finset.range (m + 1), Q m k = 1) :
    ∀ (L n : ℕ), ∑ k ∈ Finset.range (n + 1), KPowK L Q n k = 1 := by
  intro L
  induction L with
  | zero =>
    intro n
    simp only [KPowK]
    rw [Finset.sum_ite_eq' (Finset.range (n + 1)) n (fun _ => (1 : ℝ)),
      if_pos (Finset.self_mem_range_succ n)]
  | succ L ih =>
    intro n
    simp only [KPowK, KCompK]
    -- ∑_k ∑_j Q n j · (KPowK L Q) j k  =  ∑_j Q n j · ∑_k (KPowK L Q) j k
    rw [Finset.sum_comm]
    have : ∀ j ∈ Finset.range (n + 1),
        ∑ k ∈ Finset.range (n + 1), Q n j * KPowK L Q j k = Q n j := by
      intro j hj
      rw [Finset.mem_range] at hj
      rw [← Finset.mul_sum]
      -- truncate the inner sum from range (n+1) to range (j+1)
      have htrunc : ∑ k ∈ Finset.range (n + 1), KPowK L Q j k
          = ∑ k ∈ Finset.range (j + 1), KPowK L Q j k := by
        have hsub : Finset.range (j + 1) ⊆ Finset.range (n + 1) := by
          intro x hx
          rw [Finset.mem_range] at hx ⊢
          exact lt_of_lt_of_le hx (Nat.succ_le_succ (Nat.lt_succ_iff.mp hj))
        refine (Finset.sum_subset hsub ?_).symm
        intro k _ hks
        rw [Finset.mem_range] at hks
        exact KPowK_support L (Nat.not_lt.mp hks)
      rw [htrunc, ih j, mul_one]
    rw [Finset.sum_congr rfl this, hQrow n]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
