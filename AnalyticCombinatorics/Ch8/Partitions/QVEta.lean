import AnalyticCombinatorics.Ch8.Partitions.QVTelescope

/-!
# R7 Fact B via Doeblin: η-robust lower quadratic variation

For an η-approximate martingale (`|∑ K x z · D z − D x| ≤ η`), the second-moment drift is
`locVar x + 2·D x·e` with `e = ∑ K x z D z − D x` the drift error; since `2 D x e ≥ −2Rη` (where
`|D| ≤ R`), telescoping gives

  `E[D_T²] ≥ E[D_0²] + (v₀ − 2Rη)·T`.

With `η ~ 1/r²` and `R ~ r`, the correction `2Rη ~ 1/r → 0`, so the effective variance `v₀ − 2Rη → v₀`
and the lower QV survives.  Deterministic finite-sum.  Opus-authored.
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {ι : Type*} [Fintype ι]

/-- Unconditional second-moment drift identity (no martingale needed). -/
lemma sq_drift_id (K : ι → ι → ℝ) (D : ι → ℝ) (x : ι) (hKsum : ∑ z, K x z = 1) :
    (∑ z, K x z * (D z) ^ 2) - (D x) ^ 2
      = locVar K D x + 2 * (D x) * ((∑ z, K x z * D z) - D x) := by
  unfold locVar
  have hexp : ∀ z, K x z * (D z - D x) ^ 2
      = K x z * (D z) ^ 2 - (2 * D x) * (K x z * D z) + (D x) ^ 2 * K x z := fun z => by ring
  rw [Finset.sum_congr rfl (fun z _ => hexp z), Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, hKsum]
  ring

/-- η-robust per-step second-moment drift lower bound. -/
lemma sq_drift_ge_eta (K : ι → ι → ℝ) (D : ι → ℝ) (v0 η R : ℝ) (x : ι) (hKsum : ∑ z, K x z = 1)
    (hmarteta : |(∑ z, K x z * D z) - D x| ≤ η) (hlvge : v0 ≤ locVar K D x) (hR : |D x| ≤ R) :
    v0 - 2 * R * η ≤ (∑ z, K x z * (D z) ^ 2) - (D x) ^ 2 := by
  rw [sq_drift_id K D x hKsum]
  rcases abs_le.1 hmarteta with ⟨hlo, hhi⟩
  have hRDx1 : 0 ≤ R + D x := by linarith [hR, neg_abs_le (D x)]
  have hRDx2 : 0 ≤ R - D x := by linarith [hR, le_abs_self (D x)]
  have hcross : -(2 * R * η) ≤ 2 * (D x) * ((∑ z, K x z * D z) - D x) := by
    nlinarith [mul_nonneg hRDx1 (by linarith [hlo] : (0:ℝ) ≤ η + ((∑ z, K x z * D z) - D x)),
      mul_nonneg hRDx2 (by linarith [hhi] : (0:ℝ) ≤ η - ((∑ z, K x z * D z) - D x))]
  linarith [hlvge, hcross]

/-- **η-robust lower quadratic variation.** -/
theorem sq_moment_ge_eta (K : ι → ι → ℝ) (D : ι → ℝ) (μ0 : ι → ℝ) (v0 η R : ℝ)
    (hKnn : ∀ x z, 0 ≤ K x z) (hKsum : ∀ x, ∑ z, K x z = 1)
    (hmarteta : ∀ x, |(∑ z, K x z * D z) - D x| ≤ η) (hμ0nn : ∀ x, 0 ≤ μ0 x) (hμ0sum : ∑ x, μ0 x = 1)
    (hlvge : ∀ x, v0 ≤ locVar K D x) (hR : ∀ x, |D x| ≤ R) (T : ℕ) :
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
              (sq_drift_ge_eta K D v0 η R x (hKsum x) (hmarteta x) (hlvge x) (hR x))
              (distPow_nonneg K μ0 hKnn hμ0nn T x)
    push_cast
    nlinarith [ih, hstep]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
