import AnalyticCombinatorics.Ch8.Partitions.MomentBounds

/-!
# R7 Fact B via Doeblin: assembling the occupation lower bound

Closed-form fourth-moment bound `E[D_T⁴] ≤ E[D_0⁴] + 8b²E[D_0²]·T + 8b⁴·T² + 3b⁴·T` (substituting the
upper QV into the fourth-moment telescoping), plus the reusable local-variance bound `locVar ≤ b²`.
These feed the Paley–Zygmund anti-concentration to give `E|D_T| → ∞`, hence (via Tanaka) the window
occupation `→ ∞`.  Deterministic finite-sum.  Opus-authored.
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {ι : Type*} [Fintype ι]

/-- Local variance is bounded by the squared increment bound. -/
lemma locVar_le (K : ι → ι → ℝ) (D : ι → ℝ) (b : ℝ) (x : ι) (hKnn : ∀ z, 0 ≤ K x z)
    (hKsum : ∑ z, K x z = 1) (hbinc : ∀ z, K x z ≠ 0 → |D z - D x| ≤ b) :
    locVar K D x ≤ b ^ 2 := by
  unfold locVar
  calc ∑ z, K x z * (D z - D x) ^ 2 ≤ ∑ z, K x z * b ^ 2 := by
        refine Finset.sum_le_sum (fun z _ => ?_)
        by_cases hz : K x z = 0
        · rw [hz, zero_mul, zero_mul]
        · refine mul_le_mul_of_nonneg_left ?_ (hKnn z)
          have := hbinc z hz
          nlinarith [abs_nonneg (D z - D x), sq_abs (D z - D x), this]
    _ = b ^ 2 := by rw [← Finset.sum_mul, hKsum, one_mul]

/-- **Closed-form fourth-moment bound** (quadratic in `T`). -/
theorem fourth_moment_le_quadratic (K : ι → ι → ℝ) (D : ι → ℝ) (μ0 : ι → ℝ) (b : ℝ) (hbnn : 0 ≤ b)
    (hKnn : ∀ x z, 0 ≤ K x z) (hKsum : ∀ x, ∑ z, K x z = 1) (hmart : ∀ x, ∑ z, K x z * D z = D x)
    (hbinc : ∀ x z, K x z ≠ 0 → |D z - D x| ≤ b) (hμ0nn : ∀ x, 0 ≤ μ0 x) (hμ0sum : ∑ x, μ0 x = 1)
    (T : ℕ) :
    (∑ x, distPow K μ0 T x * (D x) ^ 4)
      ≤ (∑ x, μ0 x * (D x) ^ 4) + 8 * b ^ 2 * (∑ x, μ0 x * (D x) ^ 2) * T
        + 8 * b ^ 4 * (T : ℝ) ^ 2 + 3 * b ^ 4 * T := by
  have htel := fourth_moment_telescope_le K D μ0 b hbnn hKnn hKsum hmart hbinc hμ0nn hμ0sum T
  have hlv : ∀ x, locVar K D x ≤ b ^ 2 := fun x => locVar_le K D b x (hKnn x) (hKsum x) (hbinc x)
  set E0 := ∑ x, μ0 x * (D x) ^ 2 with hE0
  have hbound : (∑ t ∈ Finset.range T,
        (8 * b ^ 2 * (∑ x, distPow K μ0 t x * (D x) ^ 2) + 3 * b ^ 4))
      ≤ 8 * b ^ 2 * E0 * T + 8 * b ^ 4 * (T : ℝ) ^ 2 + 3 * b ^ 4 * T := by
    calc (∑ t ∈ Finset.range T,
            (8 * b ^ 2 * (∑ x, distPow K μ0 t x * (D x) ^ 2) + 3 * b ^ 4))
        ≤ ∑ _t ∈ Finset.range T, (8 * b ^ 2 * E0 + 8 * b ^ 4 * (T : ℝ) + 3 * b ^ 4) := by
          refine Finset.sum_le_sum (fun t ht => ?_)
          have hsq := sq_moment_le K D μ0 (b ^ 2) hKnn hKsum hmart hμ0nn hμ0sum hlv t
          have htle : (t : ℝ) ≤ T := by exact_mod_cast le_of_lt (Finset.mem_range.1 ht)
          have hb2 : (0 : ℝ) ≤ 8 * b ^ 2 := by positivity
          have hb4 : (0 : ℝ) ≤ 8 * b ^ 4 := by positivity
          nlinarith [mul_le_mul_of_nonneg_left hsq hb2, mul_le_mul_of_nonneg_left htle hb4]
      _ = (8 * b ^ 2 * E0 + 8 * b ^ 4 * (T : ℝ) + 3 * b ^ 4) * T := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
      _ = 8 * b ^ 2 * E0 * T + 8 * b ^ 4 * (T : ℝ) ^ 2 + 3 * b ^ 4 * T := by ring
  linarith [htel, hbound]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
