import AnalyticCombinatorics.Ch8.Partitions.TanakaTelescope

/-!
# R7 Fact B via Doeblin: quadratic-variation telescoping (Doob decomposition for `D²`)

For a mean-preserving kernel, `D²` has Doob compensator equal to the cumulative local variance
`locVar x = ∑_z K x z (D z − D x)²`:

  `E[D_T²] − E[D_0²] = ∑_{t<T} ∑_x distPow t x · locVar x`.

With a uniform local-variance lower bound `v₀ ≤ locVar` this gives `E[D_T²] ≥ E[D_0²] + v₀·T`, the lower
quadratic-variation feeding the Paley–Zygmund bound `E|D_T| ≥ c√T`.  Deterministic finite-sum.
Opus-authored.
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {ι : Type*} [Fintype ι]

/-- Local variance (one-step quadratic-variation increment) at `x`. -/
def locVar (K : ι → ι → ℝ) (D : ι → ℝ) (x : ι) : ℝ := ∑ z, K x z * (D z - D x) ^ 2

/-- For a mean-preserving step, the second-moment drift equals the local variance. -/
lemma locVar_eq (K : ι → ι → ℝ) (D : ι → ℝ) (x : ι) (hKsum : ∑ z, K x z = 1)
    (hmart : ∑ z, K x z * D z = D x) :
    locVar K D x = (∑ z, K x z * (D z) ^ 2) - (D x) ^ 2 := by
  unfold locVar
  have expand : ∀ z, K x z * (D z - D x) ^ 2
      = K x z * (D z) ^ 2 - (2 * D x) * (K x z * D z) + (D x) ^ 2 * K x z := by
    intro z; ring
  rw [Finset.sum_congr rfl (fun z _ => expand z), Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, hmart, hKsum]
  ring

/-- The law `distPow` stays a probability distribution. -/
lemma distPow_sum (K : ι → ι → ℝ) (μ0 : ι → ℝ) (hKsum : ∀ x, ∑ z, K x z = 1)
    (hμ0 : ∑ x, μ0 x = 1) : ∀ t, ∑ x, distPow K μ0 t x = 1 := by
  intro t
  induction t with
  | zero => exact hμ0
  | succ t ih =>
    simp only [distPow]
    rw [Finset.sum_comm,
      Finset.sum_congr rfl (fun x _ => by rw [← Finset.mul_sum, hKsum x, mul_one])]
    exact ih

/-- **Quadratic-variation telescoping (Doob for `D²`).** -/
theorem sq_moment_telescope (K : ι → ι → ℝ) (D : ι → ℝ) (μ0 : ι → ℝ)
    (hKsum : ∀ x, ∑ z, K x z = 1) (hmart : ∀ x, ∑ z, K x z * D z = D x) (T : ℕ) :
    (∑ x, distPow K μ0 T x * (D x) ^ 2) - (∑ x, μ0 x * (D x) ^ 2)
      = ∑ t ∈ Finset.range T, ∑ x, distPow K μ0 t x * locVar K D x := by
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
    have hstep : (∑ x, distPow K μ0 (T + 1) x * (D x) ^ 2)
        - (∑ x, distPow K μ0 T x * (D x) ^ 2)
        = ∑ x, distPow K μ0 T x * locVar K D x := by
      rw [hswap, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [← mul_sub, locVar_eq K D x (hKsum x) (hmart x)]
    rw [Finset.sum_range_succ]
    linarith [ih, hstep]

/-- **Lower quadratic variation.** With a uniform local-variance lower bound, `E[D_T²] ≥ E[D_0²] + v₀·T`. -/
theorem sq_moment_ge (K : ι → ι → ℝ) (D : ι → ℝ) (μ0 : ι → ℝ) (v0 : ℝ)
    (hKnn : ∀ x z, 0 ≤ K x z) (hKsum : ∀ x, ∑ z, K x z = 1) (hmart : ∀ x, ∑ z, K x z * D z = D x)
    (hμ0nn : ∀ x, 0 ≤ μ0 x) (hμ0sum : ∑ x, μ0 x = 1) (hv0 : ∀ x, v0 ≤ locVar K D x) (T : ℕ) :
    (∑ x, μ0 x * (D x) ^ 2) + v0 * T ≤ ∑ x, distPow K μ0 T x * (D x) ^ 2 := by
  have htel := sq_moment_telescope K D μ0 hKsum hmart T
  have hge : ∀ t, v0 ≤ ∑ x, distPow K μ0 t x * locVar K D x := by
    intro t
    calc v0 = v0 * (∑ x, distPow K μ0 t x) := by rw [distPow_sum K μ0 hKsum hμ0sum t, mul_one]
      _ = ∑ x, distPow K μ0 t x * v0 := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun x _ => by ring)
      _ ≤ ∑ x, distPow K μ0 t x * locVar K D x :=
          Finset.sum_le_sum (fun x _ =>
            mul_le_mul_of_nonneg_left (hv0 x) (distPow_nonneg K μ0 hKnn hμ0nn t x))
  have hsum : v0 * T ≤ ∑ t ∈ Finset.range T, ∑ x, distPow K μ0 t x * locVar K D x := by
    calc v0 * T = ∑ _t ∈ Finset.range T, v0 := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
      _ ≤ ∑ t ∈ Finset.range T, ∑ x, distPow K μ0 t x * locVar K D x :=
          Finset.sum_le_sum (fun t _ => hge t)
  linarith [htel, hsum]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
