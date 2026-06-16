import AnalyticCombinatorics.Ch4.Analytic.LogFaithful

/-!
# Multiplicativity of the generalized-binomial series `oneSubCpowGF`

`oneSubCpowGF α` is the formal power series of `(1-z)^{-α}`.  This file proves the
exponent-additivity

  `oneSubCpowGF α · oneSubCpowGF β = oneSubCpowGF (α + β)`,

the formal counterpart of `(1-z)^{-α}·(1-z)^{-β} = (1-z)^{-(α+β)}`.  The proof is by
analytic uniqueness: both sides realize `(1-z)^{-(α+β)}` on the unit ball (the left
side via the banked Cauchy product `hasSum_powerSeries_mul` and `Complex.cpow_add`),
hence their `toFMLS` agree and so do their coefficients.

Consequence: `binCoeffℂ 1 = 1`, `(mapℂ permutations.egf)^k = oneSubCpowGF k`, which feed
the integer family of cycle-marked permutation tuples.
-/

open Complex Filter
open scoped Topology BigOperators

namespace AnalyticCombinatorics

/-- `oneSubCpowGF` realizes `(1-z)^{-α}` as a `HasFPowerSeriesAt` at `0`. -/
lemma oneSubCpowGF_hasFPowerSeriesAt (α : ℂ) :
    HasFPowerSeriesAt (fun z : ℂ => (1 - z) ^ (-α)) (PowerSeries.toFMLS (oneSubCpowGF α)) 0 := by
  rw [hasFPowerSeriesAt_iff]
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with z hz
  have hz_norm : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hz
  simpa [PowerSeries.coeff_toFMLS, smul_eq_mul, mul_comm] using oneSubCpowGF_hasSum (α := α) hz_norm

/-- **Exponent additivity** of `oneSubCpowGF`. -/
theorem oneSubCpowGF_add (α β : ℂ) :
    oneSubCpowGF α * oneSubCpowGF β = oneSubCpowGF (α + β) := by
  have hF : HasFPowerSeriesAt (fun z : ℂ => (1 - z) ^ (-(α + β)))
      (PowerSeries.toFMLS (oneSubCpowGF α * oneSubCpowGF β)) 0 := by
    rw [hasFPowerSeriesAt_iff]
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with z hz
    have hz_norm : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hz
    have hz0 : (1 : ℂ) - z ≠ 0 := by
      intro h; rw [sub_eq_zero] at h; rw [← h] at hz_norm; simp at hz_norm
    have hprod := hasSum_powerSeries_mul (oneSubCpowGF α) (oneSubCpowGF β)
      (oneSubCpowGF_hasSum (α := α) hz_norm) (oneSubCpowGF_hasSum (α := β) hz_norm)
      (oneSubCpowGF_summable_norm (α := α) hz_norm) (oneSubCpowGF_summable_norm (α := β) hz_norm)
    rw [← Complex.cpow_add _ _ hz0, show (-α + -β) = -(α + β) by ring] at hprod
    simpa [PowerSeries.coeff_toFMLS, smul_eq_mul, mul_comm] using hprod
  have hG : HasFPowerSeriesAt (fun z : ℂ => (1 - z) ^ (-(α + β)))
      (PowerSeries.toFMLS (oneSubCpowGF (α + β))) 0 := oneSubCpowGF_hasFPowerSeriesAt (α + β)
  have heq := hF.eq_formalMultilinearSeries_of_eventually hG (Filter.EventuallyEq.refl _ _)
  ext n
  have hcoeff := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) heq
  simpa [PowerSeries.coeff_toFMLS] using hcoeff

/-- The binomial coefficients of `(1-z)^{-1}` are all `1`. -/
lemma binCoeffℂ_one (n : ℕ) : binCoeffℂ 1 n = 1 := by
  induction n with
  | zero => simp [binCoeffℂ]
  | succ k ih =>
    have hrec := binCoeffℂ_succ 1 k
    rw [ih, mul_one] at hrec
    have hk1 : ((k : ℂ) + 1) ≠ 0 := by
      have : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have h2 : ((k : ℝ) + 1 : ℂ) ≠ 0 := by exact_mod_cast this.ne'
      push_cast at h2 ⊢; exact h2
    have : ((k : ℂ) + 1) * binCoeffℂ 1 (k + 1) = ((k : ℂ) + 1) * 1 := by
      rw [mul_one]; rw [hrec]; ring
    exact mul_left_cancel₀ hk1 this

end AnalyticCombinatorics
