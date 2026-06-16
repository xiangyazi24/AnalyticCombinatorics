import AnalyticCombinatorics.Ch4.Analytic.LogSingularity

/-!
# Coefficient scale for the squared-logarithm singularity `(1-z)^{-α} log²(1/(1-z))`

The `log²` model `(1-z)^{-α}·(-log(1-z))²` has `[zⁿ]` coefficient (morally `∂²_α` of the
binomial coefficient)

  `logSqSingularityScale α n := Ring.choose (α+n-1) n · ((shiftedHarmonic α n)² - shiftedHarmonic2 α n)`,

`shiftedHarmonic2 α n := ∑_{j<n} (α+j)⁻²`.  This file proves

  `logSqSingularityScale α n ~ n^{α-1}/Γ(α) · (log n)²`,

extending `logSingularityCoeff_isEquivalent`.  Since `0 ≤ shiftedHarmonic2 ≤ α⁻¹·shiftedHarmonic`
(termwise `(α+j)⁻² ≤ α⁻¹(α+j)⁻¹`), `shiftedHarmonic2 = O(log) = o(log²)`, so the bracket is
`~ (shiftedHarmonic)² ~ log²`.
-/

open Filter Asymptotics
open scoped Topology BigOperators

noncomputable section

/-- `∑_{j<n} (α+j)⁻²`, the second-order shifted harmonic sum. -/
def shiftedHarmonic2 (α : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, ((α + j) ^ 2)⁻¹

/-- The squared-logarithm coefficient scale. -/
def logSqSingularityScale (α : ℝ) (n : ℕ) : ℝ :=
  Ring.choose (α + n - 1) n * ((shiftedHarmonic α n) ^ 2 - shiftedHarmonic2 α n)

lemma shiftedHarmonic2_nonneg {α : ℝ} (hα : 0 < α) (n : ℕ) : 0 ≤ shiftedHarmonic2 α n :=
  Finset.sum_nonneg (fun j _ => by positivity)

/-- Termwise `(α+j)⁻² ≤ α⁻¹(α+j)⁻¹`, summed. -/
lemma shiftedHarmonic2_le {α : ℝ} (hα : 0 < α) (n : ℕ) :
    shiftedHarmonic2 α n ≤ α⁻¹ * shiftedHarmonic α n := by
  rw [shiftedHarmonic2, shiftedHarmonic, Finset.mul_sum]
  refine Finset.sum_le_sum (fun j _ => ?_)
  have h1 : 0 < α + (j : ℝ) := by positivity
  have hsq : α * (α + (j : ℝ)) ≤ (α + (j : ℝ)) ^ 2 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) j]
  calc ((α + (j : ℝ)) ^ 2)⁻¹ ≤ (α * (α + (j : ℝ)))⁻¹ := inv_anti₀ (by positivity) hsq
    _ = α⁻¹ * (α + (j : ℝ))⁻¹ := by rw [mul_inv]

theorem logSqSingularityScale_isEquivalent {α : ℝ} (hα : 1 < α) :
    (fun n : ℕ => logSqSingularityScale α n) ~[atTop]
      (fun n : ℕ => ((n : ℝ) ^ (α - 1) / Real.Gamma α) * (Real.log n) ^ 2) := by
  have hα0 : 0 < α := by linarith
  have hchoose := choose_standard_scale_real (α := α)
    (fun m => ne_of_gt (by have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m; linarith))
  have hH : (fun n : ℕ => shiftedHarmonic α n) ~[atTop] (fun n : ℕ => Real.log n) :=
    shiftedHarmonic_isEquivalent_log hα0
  have hlog_atTop : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  -- (shiftedHarmonic)² ~ (log)²
  have hHsq : (fun n : ℕ => (shiftedHarmonic α n) ^ 2)
      ~[atTop] (fun n : ℕ => (Real.log n) ^ 2) := by
    refine ((hH.mul hH).congr_left ?_).congr_right ?_
    · filter_upwards with n; simp [Pi.mul_apply, pow_two]
    · filter_upwards with n; simp [Pi.mul_apply, pow_two]
  -- shiftedHarmonic2 = o(log²)
  have hH2_bigO_log : (fun n : ℕ => shiftedHarmonic2 α n) =O[atTop] (fun n : ℕ => Real.log n) := by
    have hbound : (fun n : ℕ => shiftedHarmonic2 α n) =O[atTop]
        (fun n : ℕ => shiftedHarmonic α n) := by
      refine IsBigO.of_bound α⁻¹ (Eventually.of_forall fun n => ?_)
      have hHnn : 0 ≤ shiftedHarmonic α n := Finset.sum_nonneg fun j _ => by positivity
      rw [Real.norm_of_nonneg (shiftedHarmonic2_nonneg hα0 n), Real.norm_of_nonneg hHnn]
      exact shiftedHarmonic2_le hα0 n
    exact hbound.trans hH.isBigO
  have hlog_littleO_sq : (fun n : ℕ => Real.log n) =o[atTop] (fun n : ℕ => (Real.log n) ^ 2) := by
    have hg : ∀ᶠ n : ℕ in atTop, (Real.log n) ^ 2 = 0 → Real.log n = 0 := by
      filter_upwards [hlog_atTop.eventually_gt_atTop 0] with n hn h0
      exact absurd h0 (by positivity)
    rw [Asymptotics.isLittleO_iff_tendsto' hg]
    have heq : (fun n : ℕ => Real.log n / (Real.log n) ^ 2) =ᶠ[atTop]
        (fun n : ℕ => (Real.log n)⁻¹) := by
      filter_upwards [hlog_atTop.eventually_gt_atTop 0] with n hn
      rw [pow_two, div_mul_eq_div_div, div_self hn.ne', one_div]
    rw [tendsto_congr' heq]
    exact tendsto_inv_atTop_zero.comp hlog_atTop
  have hH2_littleO : (fun n : ℕ => shiftedHarmonic2 α n) =o[atTop] (fun n : ℕ => (Real.log n) ^ 2) :=
    hH2_bigO_log.trans_isLittleO hlog_littleO_sq
  have hbracket : (fun n : ℕ => (shiftedHarmonic α n) ^ 2 - shiftedHarmonic2 α n)
      ~[atTop] (fun n : ℕ => (Real.log n) ^ 2) :=
    hHsq.sub_isLittleO hH2_littleO
  refine ((hchoose.mul hbracket).congr_left ?_).congr_right ?_
  · filter_upwards with n; simp [Pi.mul_apply, logSqSingularityScale]
  · filter_upwards with n; simp [Pi.mul_apply]
