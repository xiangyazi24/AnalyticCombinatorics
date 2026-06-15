import AnalyticCombinatorics.Ch8.Partitions.QVTelescope

/-!
# L¹ stability of Markov evolution (occupation transfer)

If two stochastic kernels `K`, `K'` are within per-step `L¹` distance `ε` (i.e.
`∀ x, ∑_z |K x z − K' x z| ≤ ε`), then their `t`-step laws from a common start are within `t·ε`:

  `∑_z |distPow K μ₀ t z − distPow K' μ₀ t z| ≤ t·ε`.

This is the route-independent transfer primitive: it lets occupation lower bounds proved for a
truncated kernel `K'` be transported to the original soft-tailed kernel `K`, the discrepancy over a
horizon `M` being `≤ ε·∑_{t<M} t`.  Deterministic finite-sum.
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {ι : Type*} [Fintype ι]

/-- **L¹ stability:** the `t`-step laws of two stochastic kernels within per-step `L¹` distance `ε`
differ by at most `t·ε` in `L¹`. -/
lemma distPow_L1_le (K K' : ι → ι → ℝ) (μ0 : ι → ℝ) (ε : ℝ)
    (hKnn : ∀ x z, 0 ≤ K x z) (hKsum : ∀ x, ∑ z, K x z = 1)
    (hK'nn : ∀ x z, 0 ≤ K' x z) (hK'sum : ∀ x, ∑ z, K' x z = 1)
    (hμ0nn : ∀ x, 0 ≤ μ0 x) (hμ0sum : ∑ x, μ0 x = 1)
    (hclose : ∀ x, (∑ z, |K x z - K' x z|) ≤ ε) :
    ∀ t, (∑ z, |distPow K μ0 t z - distPow K' μ0 t z|) ≤ t * ε := by
  intro t
  induction t with
  | zero => simp [distPow]
  | succ t ih =>
    -- per-coordinate split
    have hz : ∀ z, |distPow K μ0 (t + 1) z - distPow K' μ0 (t + 1) z|
        ≤ (∑ x, |distPow K μ0 t x - distPow K' μ0 t x| * K x z)
          + ∑ x, distPow K' μ0 t x * |K x z - K' x z| := by
      intro z
      simp only [distPow]
      rw [← Finset.sum_sub_distrib]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum (fun x _ => ?_)
      have hsplit : distPow K μ0 t x * K x z - distPow K' μ0 t x * K' x z
          = (distPow K μ0 t x - distPow K' μ0 t x) * K x z
            + distPow K' μ0 t x * (K x z - K' x z) := by ring
      rw [hsplit]
      refine le_trans (abs_add_le _ _) ?_
      rw [abs_mul, abs_mul, abs_of_nonneg (hKnn x z),
        abs_of_nonneg (distPow_nonneg K' μ0 hK'nn hμ0nn t x)]
    -- sum over z and use sum_comm
    calc (∑ z, |distPow K μ0 (t + 1) z - distPow K' μ0 (t + 1) z|)
        ≤ ∑ z, ((∑ x, |distPow K μ0 t x - distPow K' μ0 t x| * K x z)
            + ∑ x, distPow K' μ0 t x * |K x z - K' x z|) := Finset.sum_le_sum (fun z _ => hz z)
      _ = (∑ x, |distPow K μ0 t x - distPow K' μ0 t x| * (∑ z, K x z))
            + ∑ x, distPow K' μ0 t x * (∑ z, |K x z - K' x z|) := by
          rw [Finset.sum_add_distrib, Finset.sum_comm]
          congr 1
          · exact Finset.sum_congr rfl (fun x _ => by rw [Finset.mul_sum])
          · rw [Finset.sum_comm]
            exact Finset.sum_congr rfl (fun x _ => by rw [Finset.mul_sum])
      _ ≤ (∑ x, |distPow K μ0 t x - distPow K' μ0 t x|) + ε := by
          refine add_le_add (le_of_eq ?_) ?_
          · exact Finset.sum_congr rfl (fun x _ => by rw [hKsum x, mul_one])
          · calc (∑ x, distPow K' μ0 t x * (∑ z, |K x z - K' x z|))
                ≤ ∑ x, distPow K' μ0 t x * ε :=
                  Finset.sum_le_sum (fun x _ =>
                    mul_le_mul_of_nonneg_left (hclose x) (distPow_nonneg K' μ0 hK'nn hμ0nn t x))
              _ = ε := by rw [← Finset.sum_mul, distPow_sum K' μ0 hK'sum hμ0sum t, one_mul]
      _ ≤ t * ε + ε := by linarith [ih]
      _ = (↑(t + 1)) * ε := by push_cast; ring

/-- **Occupation transfer:** a window-occupation lower bound for `K'` transfers to `K`, up to the
discrepancy `(∑_{t<M} t)·ε`.  (So `occ_K ≥ occ_{K'} − (∑t)·ε`.) -/
lemma occupation_transfer (K K' : ι → ι → ℝ) (μ0 : ι → ℝ) (D : ι → ℝ) (b ε : ℝ) (M : ℕ)
    (hKnn : ∀ x z, 0 ≤ K x z) (hKsum : ∀ x, ∑ z, K x z = 1)
    (hK'nn : ∀ x z, 0 ≤ K' x z) (hK'sum : ∀ x, ∑ z, K' x z = 1)
    (hμ0nn : ∀ x, 0 ≤ μ0 x) (hμ0sum : ∑ x, μ0 x = 1)
    (hclose : ∀ x, (∑ z, |K x z - K' x z|) ≤ ε) :
    (∑ t ∈ Finset.range M, ∑ x, distPow K' μ0 t x * (if |D x| ≤ b then (1 : ℝ) else 0))
      - (∑ t ∈ Finset.range M, ∑ x, distPow K μ0 t x * (if |D x| ≤ b then (1 : ℝ) else 0))
      ≤ (∑ t ∈ Finset.range M, (t : ℝ)) * ε := by
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  refine Finset.sum_le_sum (fun t _ => ?_)
  have hL1 : (∑ z, |distPow K' μ0 t z - distPow K μ0 t z|) ≤ t * ε :=
    distPow_L1_le K' K μ0 ε hK'nn hK'sum hKnn hKsum hμ0nn hμ0sum
      (fun x => by simpa [abs_sub_comm] using hclose x) t
  calc (∑ x, distPow K' μ0 t x * (if |D x| ≤ b then (1 : ℝ) else 0))
        - ∑ x, distPow K μ0 t x * (if |D x| ≤ b then (1 : ℝ) else 0)
      = ∑ x, (distPow K' μ0 t x - distPow K μ0 t x) * (if |D x| ≤ b then (1 : ℝ) else 0) := by
        rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun x _ => by ring)
    _ ≤ ∑ x, |distPow K' μ0 t x - distPow K μ0 t x| := by
        refine Finset.sum_le_sum (fun x _ => ?_)
        by_cases h : |D x| ≤ b
        · rw [if_pos h, mul_one]; exact le_abs_self _
        · rw [if_neg h, mul_zero]; exact abs_nonneg _
    _ ≤ t * ε := hL1

end AnalyticCombinatorics.Ch8.Partitions.Erdos
