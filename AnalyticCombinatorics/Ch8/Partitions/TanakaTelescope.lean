import AnalyticCombinatorics.Ch8.Partitions.TanakaStep

/-!
# R7 Fact B via Doeblin: Tanaka telescoping ⟹ window occupation lower bound

Telescoping the single-step `|D|`-drift (brick 85) over the evolving distribution `distPow K μ₀ t`
(the law of the walk after `t` steps) yields, for a mean-preserving bounded-increment kernel,

  `E|D_T| − E|D_0| ≤ b · ∑_{t<T} (window-occupation at step t)`,

i.e. `window-occupation ≥ (E|D_T| − E|D_0|)/b`.  Combined with the Paley–Zygmund bound `E|D_T| ≥ c√T`
(brick 84) and the per-step second/fourth moments of the Erdős rank-difference walk, this gives the
occupation lower bound `≥ 1/δ` that closes the Hardy–Ramanujan convergence.  All deterministic finite-sum
algebra.  Opus-authored.
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {ι : Type*} [Fintype ι]

/-- Law of the walk after `t` steps from initial distribution `μ₀` under kernel `K`. -/
def distPow (K : ι → ι → ℝ) (μ0 : ι → ℝ) : ℕ → ι → ℝ
  | 0 => μ0
  | (t + 1) => fun z => ∑ x, distPow K μ0 t x * K x z

lemma distPow_nonneg (K : ι → ι → ℝ) (μ0 : ι → ℝ) (hKnn : ∀ x z, 0 ≤ K x z)
    (hμ0 : ∀ x, 0 ≤ μ0 x) : ∀ t x, 0 ≤ distPow K μ0 t x := by
  intro t
  induction t with
  | zero => exact hμ0
  | succ t ih => exact fun z => Finset.sum_nonneg (fun x _ => mul_nonneg (ih x) (hKnn x z))

/-- The single-step `|D|`-drift is bounded by `b` on the window `{|D| ≤ b}` and vanishes off it. -/
lemma abs_drift_le_indic (K : ι → ι → ℝ) (D : ι → ℝ) (b : ℝ) (hbnn : 0 ≤ b) (x : ι)
    (hKnn : ∀ z, 0 ≤ K x z) (hKsum : ∑ z, K x z = 1)
    (hmart : ∑ z, K x z * D z = D x) (hbinc : ∀ z, K x z ≠ 0 → |D z - D x| ≤ b) :
    (∑ z, K x z * |D z|) - |D x| ≤ b * (if |D x| ≤ b then (1 : ℝ) else 0) := by
  by_cases hle : |D x| ≤ b
  · rw [if_pos hle, mul_one]
    linarith [abs_drift_le K D b x hKnn hKsum hbinc]
  · rw [if_neg hle, mul_zero]
    push_neg at hle
    have heq := abs_drift_eq_of_far K D b hbnn x hKnn hmart hbinc hle
    linarith [heq]

/-- **Tanaka telescoping ⟹ occupation lower bound.** For a mean-preserving (`∑ K x z · D z = D x`)
kernel with bounded increments `b`, the cumulative window occupation of the law `distPow K μ₀` controls
the growth of `E|D|`:
  `E|D_T| − E|D_0| ≤ b · ∑_{t<T} (window-b occupation at t)`. -/
theorem occupation_ge_tanaka (K : ι → ι → ℝ) (D : ι → ℝ) (b : ℝ) (hbnn : 0 ≤ b) (μ0 : ι → ℝ)
    (hμ0nn : ∀ x, 0 ≤ μ0 x) (hKnn : ∀ x z, 0 ≤ K x z) (hKsum : ∀ x, ∑ z, K x z = 1)
    (hmart : ∀ x, ∑ z, K x z * D z = D x) (hbinc : ∀ x z, K x z ≠ 0 → |D z - D x| ≤ b) (T : ℕ) :
    (∑ x, distPow K μ0 T x * |D x|) - (∑ x, μ0 x * |D x|)
      ≤ b * ∑ t ∈ Finset.range T,
          ∑ x, distPow K μ0 t x * (if |D x| ≤ b then (1 : ℝ) else 0) := by
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
        ≤ b * ∑ x, distPow K μ0 T x * (if |D x| ≤ b then (1 : ℝ) else 0) := by
      rw [hswap, ← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_le_sum (fun x _ => ?_)
      have hdp : 0 ≤ distPow K μ0 T x := distPow_nonneg K μ0 hKnn hμ0nn T x
      have hd := abs_drift_le_indic K D b hbnn x (hKnn x) (hKsum x) (hmart x) (hbinc x)
      rw [← mul_sub]
      calc distPow K μ0 T x * ((∑ z, K x z * |D z|) - |D x|)
          ≤ distPow K μ0 T x * (b * (if |D x| ≤ b then (1 : ℝ) else 0)) :=
            mul_le_mul_of_nonneg_left hd hdp
        _ = b * (distPow K μ0 T x * (if |D x| ≤ b then (1 : ℝ) else 0)) := by ring
    rw [Finset.sum_range_succ, mul_add]
    linarith [ih, hstep]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
