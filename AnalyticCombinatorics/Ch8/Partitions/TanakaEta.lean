import AnalyticCombinatorics.Ch8.Partitions.QVTelescope

/-!
# R7 Fact B via Doeblin: η-robust Tanaka occupation bound

The Erdős rank-difference walk is only an *approximate* martingale: `|∑_z K x z · D z − D x| ≤ η` with
`η ~ 1/r² → 0` (the mean rank-decrement is rank-dependent at next order).  This file re-derives the
Tanaka occupation bound with the drift error tracked:

  `E|D_T| − E|D_0| ≤ b · (window occupation) + η · T`,

so `occupation ≥ (E|D_T| − E|D_0| − η·T)/b`.  Off-window the `|D|`-drift is `≤ η` (not `0`); since
`η·T ≪ √T ≤ E|D_T|` at the optimal horizon `T ~ r²`, the occupation still diverges.  Deterministic
finite-sum.  Opus-authored.
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {ι : Type*} [Fintype ι]

/-- η-robust per-step `|D|`-drift: bounded by `b` on the window and by `η` off it. -/
lemma abs_drift_le_indic_eta (K : ι → ι → ℝ) (D : ι → ℝ) (b η : ℝ) (hbnn : 0 ≤ b) (hηnn : 0 ≤ η)
    (x : ι) (hKnn : ∀ z, 0 ≤ K x z) (hKsum : ∑ z, K x z = 1)
    (hmarteta : |(∑ z, K x z * D z) - D x| ≤ η) (hbinc : ∀ z, K x z ≠ 0 → |D z - D x| ≤ b) :
    (∑ z, K x z * |D z|) - |D x| ≤ b * (if |D x| ≤ b then (1 : ℝ) else 0) + η := by
  rcases abs_le.1 hmarteta with ⟨hlo, hhi⟩
  by_cases hle : |D x| ≤ b
  · rw [if_pos hle, mul_one]
    linarith [abs_drift_le K D b x hKnn hKsum hbinc, hηnn]
  · rw [if_neg hle, mul_zero, zero_add]
    push_neg at hle
    -- off-window: all reachable D z share the sign of D x, so ∑ K |D z| = sign · ∑ K D z ≤ |D x| + η
    rcases lt_trichotomy (D x) 0 with hneg | hzero | hpos
    · have habs : |D x| = -D x := abs_of_neg hneg
      have hsum : (∑ z, K x z * |D z|) = -(∑ z, K x z * D z) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl (fun z _ => ?_)
        by_cases hz : K x z = 0
        · rw [hz, zero_mul, zero_mul, neg_zero]
        · have hbz := abs_le.1 (hbinc z hz)
          have hdz : D z < 0 := by rw [habs] at hle; linarith [hbz.2]
          rw [abs_of_neg hdz]; ring
      rw [hsum, habs]; linarith [hlo]
    · exfalso; rw [hzero] at hle; simp at hle; linarith [hbnn]
    · have habs : |D x| = D x := abs_of_pos hpos
      have hsum : (∑ z, K x z * |D z|) = ∑ z, K x z * D z := by
        refine Finset.sum_congr rfl (fun z _ => ?_)
        by_cases hz : K x z = 0
        · rw [hz, zero_mul, zero_mul]
        · have hbz := abs_le.1 (hbinc z hz)
          have hdz : 0 < D z := by rw [habs] at hle; linarith [hbz.1]
          rw [abs_of_pos hdz]
      rw [hsum, habs]; linarith [hhi]

/-- **η-robust Tanaka occupation bound.** -/
theorem occupation_ge_tanaka_eta (K : ι → ι → ℝ) (D : ι → ℝ) (b η : ℝ) (hbnn : 0 ≤ b) (hηnn : 0 ≤ η)
    (μ0 : ι → ℝ) (hμ0nn : ∀ x, 0 ≤ μ0 x) (hKnn : ∀ x z, 0 ≤ K x z) (hKsum : ∀ x, ∑ z, K x z = 1)
    (hμ0sum : ∑ x, μ0 x = 1) (hmarteta : ∀ x, |(∑ z, K x z * D z) - D x| ≤ η)
    (hbinc : ∀ x z, K x z ≠ 0 → |D z - D x| ≤ b) (T : ℕ) :
    (∑ x, distPow K μ0 T x * |D x|) - (∑ x, μ0 x * |D x|)
      ≤ b * (∑ t ∈ Finset.range T,
          ∑ x, distPow K μ0 t x * (if |D x| ≤ b then (1 : ℝ) else 0)) + η * T := by
  induction T with
  | zero => simp [distPow]
  | succ T ih =>
    have hswap : (∑ x, distPow K μ0 (T + 1) x * |D x|)
        = ∑ x, distPow K μ0 T x * (∑ z, K x z * |D z|) := by
      simp only [distPow]
      rw [show (∑ z, (∑ x, distPow K μ0 T x * K x z) * |D z|)
            = ∑ z, ∑ x, distPow K μ0 T x * K x z * |D z| from
          Finset.sum_congr rfl (fun z _ => by rw [Finset.sum_mul])]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun z _ => by ring)
    have hstep : (∑ x, distPow K μ0 (T + 1) x * |D x|) - (∑ x, distPow K μ0 T x * |D x|)
        ≤ b * (∑ x, distPow K μ0 T x * (if |D x| ≤ b then (1 : ℝ) else 0)) + η := by
      rw [hswap, ← Finset.sum_sub_distrib]
      calc (∑ x, (distPow K μ0 T x * (∑ z, K x z * |D z|) - distPow K μ0 T x * |D x|))
          ≤ ∑ x, distPow K μ0 T x * (b * (if |D x| ≤ b then (1 : ℝ) else 0) + η) := by
            refine Finset.sum_le_sum (fun x _ => ?_)
            rw [← mul_sub]
            exact mul_le_mul_of_nonneg_left
              (abs_drift_le_indic_eta K D b η hbnn hηnn x (hKnn x) (hKsum x) (hmarteta x) (hbinc x))
              (distPow_nonneg K μ0 hKnn hμ0nn T x)
        _ = b * (∑ x, distPow K μ0 T x * (if |D x| ≤ b then (1 : ℝ) else 0)) + η := by
            rw [Finset.sum_congr rfl (fun x _ =>
              show distPow K μ0 T x * (b * (if |D x| ≤ b then (1:ℝ) else 0) + η)
                = b * (distPow K μ0 T x * (if |D x| ≤ b then (1:ℝ) else 0)) + η * distPow K μ0 T x from by
                ring)]
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
              distPow_sum K μ0 hKsum hμ0sum T, mul_one]
    rw [Finset.sum_range_succ, mul_add]
    push_cast
    nlinarith [ih, hstep]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
