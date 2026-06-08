import AnalyticCombinatorics.Ch8.Partitions.QVEta

/-!
# R7 Fact B via Doeblin: one-sided (localized) lower quadratic variation

For the *conditioned* residual walk `K̂res`, the drift is NOT uniformly small: on-window it is a bounded
REPELLING drift (`D·e ≥ 0`), off-window it is the product drift (`|e| ≤ η`).  The energy/QV lower bound
needs only the ONE-SIDED bound `D x · (∑ K x z D z − D x) ≥ −R·η` (which holds in both regimes: off-window
`≥ −Rη`, on-window `≥ 0`), so the lower quadratic variation `E[D_T²] ≥ E[D_0²] + (v₀ − 2Rη)·T` survives
without uniform mart-eta.  This is the localization needed to apply the occupation argument to the
conditioned walk.  Deterministic finite-sum.  Opus-authored.
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- One-sided per-step second-moment drift lower bound (no uniform mart-eta; only `D·e ≥ −Rη`). -/
lemma sq_drift_ge_onesided {ι : Type*} [Fintype ι] (K : ι → ι → ℝ) (D : ι → ℝ) (v0 η R : ℝ) (x : ι)
    (hKsum : ∑ z, K x z = 1) (hlvge : v0 ≤ locVar K D x)
    (hcross : -(R * η) ≤ (D x) * ((∑ z, K x z * D z) - D x)) :
    v0 - 2 * R * η ≤ (∑ z, K x z * (D z) ^ 2) - (D x) ^ 2 := by
  rw [sq_drift_id K D x hKsum]; linarith [hlvge, hcross]

variable (P : α → α → ℝ) (rnk : α → ℕ) (W : ℕ)
variable (hPnn : ∀ x y, 0 ≤ P x y) (hPmass : ∀ x, ∑ y, P x y = 1)
variable (i j : α)

include hPnn hPmass in
/-- **One-sided (localized) lower quadratic variation.** -/
theorem sq_moment_ge_onesided (K : α → α → ℝ) (D : α → ℝ) (μ0 : α → ℝ) (v0 η R : ℝ)
    (hKnn : ∀ x z, 0 ≤ K x z) (hKsum : ∀ x, ∑ z, K x z = 1)
    (hμ0nn : ∀ x, 0 ≤ μ0 x) (hμ0sum : ∑ x, μ0 x = 1)
    (hlvge : ∀ x, v0 ≤ locVar K D x)
    (hcross : ∀ x, -(R * η) ≤ (D x) * ((∑ z, K x z * D z) - D x)) (T : ℕ) :
    (∑ x, μ0 x * (D x) ^ 2) + (v0 - 2 * R * η) * T ≤ ∑ x, distPow K μ0 T x * (D x) ^ 2 := by
  induction T with
  | zero => simp [distPow]
  | succ T ih =>
    have hswap : (∑ x, distPow K μ0 (T + 1) x * (D x) ^ 2)
        = ∑ x, distPow K μ0 T x * (∑ z, K x z * (D z) ^ 2) := by
      simp only [distPow]
      rw [show (∑ z, (∑ x, distPow K μ0 T x * K x z) * (D z) ^ 2)
            = ∑ z, ∑ x, distPow K μ0 T x * K x z * (D z) ^ 2 from
          Finset.sum_congr rfl (fun z _ => by rw [Finset.sum_mul])]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun z _ => by ring)
    have hstep : (v0 - 2 * R * η)
        ≤ (∑ x, distPow K μ0 (T + 1) x * (D x) ^ 2) - (∑ x, distPow K μ0 T x * (D x) ^ 2) := by
      rw [hswap, ← Finset.sum_sub_distrib]
      calc v0 - 2 * R * η = (v0 - 2 * R * η) * (∑ x, distPow K μ0 T x) := by
            rw [distPow_sum K μ0 hKsum hμ0sum T, mul_one]
        _ = ∑ x, distPow K μ0 T x * (v0 - 2 * R * η) := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun x _ => by ring)
        _ ≤ ∑ x, (distPow K μ0 T x * (∑ z, K x z * (D z) ^ 2) - distPow K μ0 T x * (D x) ^ 2) := by
            refine Finset.sum_le_sum (fun x _ => ?_)
            rw [← mul_sub]
            exact mul_le_mul_of_nonneg_left
              (sq_drift_ge_onesided K D v0 η R x (hKsum x) (hlvge x) (hcross x))
              (distPow_nonneg K μ0 hKnn hμ0nn T x)
    push_cast
    nlinarith [ih, hstep]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
