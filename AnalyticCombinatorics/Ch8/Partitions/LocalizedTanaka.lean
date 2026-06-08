import AnalyticCombinatorics.Ch8.Partitions.QVTelescope

/-!
# R7 Fact B via Doeblin: localized (off-window) Tanaka occupation bound

The conditioned residual walk has a bounded REPELLING drift on the window, but is the product walk
(approximate martingale) OFF the window.  The Tanaka `|D|`-drift bound needs the drift `≤ η` only OFF the
window (`b < |D x|`); on-window the per-step `|D|`-drift is `≤ b` regardless of the drift (triangle
inequality).  So the occupation bound `E|D_T| − E|D_0| ≤ b·(window occupation) + η·T` holds with only the
off-window drift hypothesis.  Deterministic finite-sum.  Opus-authored.
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Localized per-step `|D|`-drift: bounded by `b` on `{|D| ≤ b}` and by `η` off it (off-window drift
hypothesis only). -/
lemma abs_drift_le_indic_off (K : α → α → ℝ) (D : α → ℝ) (b η : ℝ) (hbnn : 0 ≤ b) (hηnn : 0 ≤ η)
    (x : α) (hKnn : ∀ z, 0 ≤ K x z) (hKsum : ∑ z, K x z = 1)
    (hdrift_off : b < |D x| → |(∑ z, K x z * D z) - D x| ≤ η)
    (hbinc : ∀ z, K x z ≠ 0 → |D z - D x| ≤ b) :
    (∑ z, K x z * |D z|) - |D x| ≤ b * (if |D x| ≤ b then (1 : ℝ) else 0) + η := by
  by_cases hle : |D x| ≤ b
  · rw [if_pos hle, mul_one]
    linarith [abs_drift_le K D b x hKnn hKsum hbinc, hηnn]
  · rw [if_neg hle, mul_zero, zero_add]
    push_neg at hle
    rcases abs_le.1 (hdrift_off hle) with ⟨hlo, hhi⟩
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

variable (P : α → α → ℝ) (rnk : α → ℕ) (W : ℕ)
variable (hPnn : ∀ x y, 0 ≤ P x y) (hPmass : ∀ x, ∑ y, P x y = 1)
variable (i j : α)

include hPnn hPmass in
/-- **Localized Tanaka occupation bound** (off-window drift hypothesis). -/
theorem occupation_ge_tanaka_loc (K : α → α → ℝ) (D : α → ℝ) (b η : ℝ) (hbnn : 0 ≤ b) (hηnn : 0 ≤ η)
    (μ0 : α → ℝ) (hμ0nn : ∀ x, 0 ≤ μ0 x) (hKnn : ∀ x z, 0 ≤ K x z) (hKsum : ∀ x, ∑ z, K x z = 1)
    (hμ0sum : ∑ x, μ0 x = 1)
    (hdrift_off : ∀ x, b < |D x| → |(∑ z, K x z * D z) - D x| ≤ η)
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
              (abs_drift_le_indic_off K D b η hbnn hηnn x (hKnn x) (hKsum x) (hdrift_off x) (hbinc x))
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
