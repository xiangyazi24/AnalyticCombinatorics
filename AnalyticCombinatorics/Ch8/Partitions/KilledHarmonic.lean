import AnalyticCombinatorics.Ch8.Partitions.KilledKernelPow

/-!
# R7 Fact B via Doeblin: the `P̃^L`-harmonic identity

A function `h` that is harmonic above a cutoff (`h n = ∑_{k<n} P n k · h k` for `rank n ≥ J`, and
`h n = φ n` below) is exactly harmonic for the *killed* kernel `P̃` summed over `range (n+1)`, and hence
for every power `KPowK L P̃`:  `h n = ∑_{k ∈ range (n+1)} (KPowK L P̃) n k · h k`.  Proof by induction on
`L` (one-step + `Finset.sum_comm` + support truncation).  This is the exact-harmonicity (η = 0) that
makes the Doeblin oscillation contraction error-free for `hitVal`.  Opus-authored.
-/

noncomputable section

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- Killed kernel: predecessor steps above the cutoff, identity-absorb on the boundary. -/
def killedKer (P : ℕ → ℕ → ℝ) (rank : ℕ → ℕ) (J : ℕ) : ℕ → ℕ → ℝ :=
  fun n k => if rank n < J then (if k = n then 1 else 0) else P n k

variable {P : ℕ → ℕ → ℝ} {rank : ℕ → ℕ} {J : ℕ} {h φ : ℕ → ℝ}

/-- One-step killed harmonicity (over `range (n+1)`). -/
lemma killed_harmonic_one (hPsupp : ∀ n k, n ≤ k → P n k = 0)
    (heq : ∀ n, h n = if rank n < J then φ n else ∑ k ∈ Finset.range n, P n k * h k) (n : ℕ) :
    h n = ∑ k ∈ Finset.range (n + 1), killedKer P rank J n k * h k := by
  unfold killedKer
  by_cases hb : rank n < J
  · simp only [if_pos hb, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq' (Finset.range (n + 1)) n h, if_pos (Finset.self_mem_range_succ n)]
  · simp only [if_neg hb]
    rw [Finset.sum_range_succ, hPsupp n n (le_refl n), zero_mul, add_zero, heq n, if_neg hb]

/-- `h` is harmonic for every killed power `KPowK L P̃` (summed over `range (n+1)`). -/
lemma killed_harmonic_pow (hPsupp : ∀ n k, n ≤ k → P n k = 0)
    (heq : ∀ n, h n = if rank n < J then φ n else ∑ k ∈ Finset.range n, P n k * h k) :
    ∀ (L n : ℕ), h n = ∑ k ∈ Finset.range (n + 1), KPowK L (killedKer P rank J) n k * h k := by
  intro L
  induction L with
  | zero =>
    intro n
    simp only [KPowK, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq' (Finset.range (n + 1)) n h, if_pos (Finset.self_mem_range_succ n)]
  | succ L ih =>
    intro n
    have key : ∑ k ∈ Finset.range (n + 1), KPowK (L + 1) (killedKer P rank J) n k * h k
        = ∑ j ∈ Finset.range (n + 1), killedKer P rank J n j * h j := by
      simp only [KPowK, KCompK]
      rw [Finset.sum_congr rfl (fun k _ => by rw [Finset.sum_mul])]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      simp only [mul_assoc]
      rw [← Finset.mul_sum]
      congr 1
      -- ∑_{k ∈ range (n+1)} (KPowK L P̃) j k * h k = h j
      have htrunc : ∑ k ∈ Finset.range (n + 1), KPowK L (killedKer P rank J) j k * h k
          = ∑ k ∈ Finset.range (j + 1), KPowK L (killedKer P rank J) j k * h k := by
        have hsub : Finset.range (j + 1) ⊆ Finset.range (n + 1) := by
          intro x hx
          rw [Finset.mem_range] at hx ⊢
          exact lt_of_lt_of_le hx (Nat.succ_le_succ (Nat.lt_succ_iff.mp hj))
        refine (Finset.sum_subset hsub ?_).symm
        intro k _ hks
        rw [Finset.mem_range] at hks
        have hjk : j < k := Nat.not_lt.mp hks
        rw [KPowK_support L hjk, zero_mul]
      rw [htrunc, ← ih j]
    rw [key, ← killed_harmonic_one hPsupp heq n]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
