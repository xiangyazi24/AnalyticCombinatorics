import AnalyticCombinatorics.Ch8.Partitions.FourthMoment

/-!
# R7 Fact B via Doeblin: telescoped second/fourth moment bounds

Telescoping the per-step bounds:
* upper quadratic variation `E[D_T²] ≤ E[D_0²] + b²·T`  (`sq_moment_le`, from `locVar ≤ b²`);
* fourth-moment growth `E[D_T⁴] − E[D_0⁴] ≤ ∑_{t<T} (8 b² E[D_t²] + 3 b⁴)`  (`fourth_moment_telescope_le`,
  from the per-step `fourth_drift_le`).

Together with the lower QV (`sq_moment_ge`) and Paley–Zygmund (`mean_sq_cubed_le`), these give
`E|D_T| ≥ c√T`, feeding the Tanaka occupation lower bound.  Deterministic finite-sum.  Opus-authored.
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {ι : Type*} [Fintype ι]

/-- **Upper quadratic variation.** With `locVar ≤ b²`, `E[D_T²] ≤ E[D_0²] + b²·T`. -/
theorem sq_moment_le (K : ι → ι → ℝ) (D : ι → ℝ) (μ0 : ι → ℝ) (b2 : ℝ)
    (hKnn : ∀ x z, 0 ≤ K x z) (hKsum : ∀ x, ∑ z, K x z = 1) (hmart : ∀ x, ∑ z, K x z * D z = D x)
    (hμ0nn : ∀ x, 0 ≤ μ0 x) (hμ0sum : ∑ x, μ0 x = 1) (hlv : ∀ x, locVar K D x ≤ b2) (T : ℕ) :
    (∑ x, distPow K μ0 T x * (D x) ^ 2) ≤ (∑ x, μ0 x * (D x) ^ 2) + b2 * T := by
  have htel := sq_moment_telescope K D μ0 hKsum hmart T
  have hle : ∀ t, (∑ x, distPow K μ0 t x * locVar K D x) ≤ b2 := by
    intro t
    calc ∑ x, distPow K μ0 t x * locVar K D x ≤ ∑ x, distPow K μ0 t x * b2 :=
          Finset.sum_le_sum (fun x _ =>
            mul_le_mul_of_nonneg_left (hlv x) (distPow_nonneg K μ0 hKnn hμ0nn t x))
      _ = b2 := by rw [← Finset.sum_mul, distPow_sum K μ0 hKsum hμ0sum t, one_mul]
  have hsum : (∑ t ∈ Finset.range T, ∑ x, distPow K μ0 t x * locVar K D x) ≤ b2 * T := by
    calc (∑ t ∈ Finset.range T, ∑ x, distPow K μ0 t x * locVar K D x)
        ≤ ∑ _t ∈ Finset.range T, b2 := Finset.sum_le_sum (fun t _ => hle t)
      _ = b2 * T := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  linarith [htel, hsum]

/-- **Fourth-moment telescoping.** -/
theorem fourth_moment_telescope_le (K : ι → ι → ℝ) (D : ι → ℝ) (μ0 : ι → ℝ) (b : ℝ) (hbnn : 0 ≤ b)
    (hKnn : ∀ x z, 0 ≤ K x z) (hKsum : ∀ x, ∑ z, K x z = 1) (hmart : ∀ x, ∑ z, K x z * D z = D x)
    (hbinc : ∀ x z, K x z ≠ 0 → |D z - D x| ≤ b) (hμ0nn : ∀ x, 0 ≤ μ0 x) (hμ0sum : ∑ x, μ0 x = 1)
    (T : ℕ) :
    (∑ x, distPow K μ0 T x * (D x) ^ 4) - (∑ x, μ0 x * (D x) ^ 4)
      ≤ ∑ t ∈ Finset.range T, (8 * b ^ 2 * (∑ x, distPow K μ0 t x * (D x) ^ 2) + 3 * b ^ 4) := by
  induction T with
  | zero => simp [distPow]
  | succ T ih =>
    have hswap : (∑ x, distPow K μ0 (T + 1) x * (D x) ^ 4)
        = ∑ x, distPow K μ0 T x * (∑ z, K x z * (D z) ^ 4) := by
      simp only [distPow]
      rw [show (∑ z, (∑ x, distPow K μ0 T x * K x z) * (D z) ^ 4)
            = ∑ z, ∑ x, distPow K μ0 T x * K x z * (D z) ^ 4 from
          Finset.sum_congr rfl (fun z _ => by rw [Finset.sum_mul])]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun z _ => by ring)
    have hstep : (∑ x, distPow K μ0 (T + 1) x * (D x) ^ 4)
        - (∑ x, distPow K μ0 T x * (D x) ^ 4)
        ≤ 8 * b ^ 2 * (∑ x, distPow K μ0 T x * (D x) ^ 2) + 3 * b ^ 4 := by
      rw [hswap, ← Finset.sum_sub_distrib]
      calc (∑ x, (distPow K μ0 T x * (∑ z, K x z * (D z) ^ 4) - distPow K μ0 T x * (D x) ^ 4))
          = ∑ x, distPow K μ0 T x * ((∑ z, K x z * (D z) ^ 4) - (D x) ^ 4) := by
            refine Finset.sum_congr rfl (fun x _ => by ring)
        _ ≤ ∑ x, distPow K μ0 T x * (8 * b ^ 2 * (D x) ^ 2 + 3 * b ^ 4) :=
            Finset.sum_le_sum (fun x _ =>
              mul_le_mul_of_nonneg_left
                (fourth_drift_le K D b hbnn x (hKnn x) (hKsum x) (hmart x) (hbinc x))
                (distPow_nonneg K μ0 hKnn hμ0nn T x))
        _ = 8 * b ^ 2 * (∑ x, distPow K μ0 T x * (D x) ^ 2) + 3 * b ^ 4 := by
            rw [Finset.sum_congr rfl (fun x _ =>
              show distPow K μ0 T x * (8 * b ^ 2 * (D x) ^ 2 + 3 * b ^ 4)
                = 8 * b ^ 2 * (distPow K μ0 T x * (D x) ^ 2) + 3 * b ^ 4 * distPow K μ0 T x from by
                ring)]
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
              distPow_sum K μ0 hKsum hμ0sum T, mul_one]
    rw [Finset.sum_range_succ]
    linarith [ih, hstep]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
