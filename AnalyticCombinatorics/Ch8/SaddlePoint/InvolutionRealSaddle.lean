import AnalyticCombinatorics.Ch8.SaddlePoint.InvolutionHAdmissible
import AnalyticCombinatorics.Ch4.Analytic.RealAsymptotics

/-!
# Involutions: the classical Moser–Wyman real saddle asymptotic

`involution_count_over_factorial_isEquivalent_saddle` (InvolutionHAdmissible) gives the abstract
H-admissible saddle estimate for the number of involutions `I_n = parts12.set.counts n` (permutations
with all cycles of length 1 or 2; EGF `exp(z + z²/2)`).  This file realifies the abstract scale to the
recognizable Moser–Wyman formula

  `I_n / n! ~ exp(r_n + r_n²/2) / ( r_n^n · √(2π · (r_n + 2 r_n²)) )`,   `r_n + r_n² = n`,

with `r_n = (√(1+4n) − 1)/2`.  "Unfold and realify" of `saddleScale`, mirroring `BellRealSaddle`.
-/

noncomputable section

open Filter Asymptotics
open scoped Topology Real

namespace InvolutionHAdmissible

/-- The classical real Moser–Wyman involution saddle scale. -/
noncomputable def involRealSaddleScale (n : ℕ) : ℝ :=
  Real.exp (involSaddleRadius n + (involSaddleRadius n) ^ 2 / 2) /
    ((involSaddleRadius n) ^ n *
      Real.sqrt (2 * Real.pi * involSaddleBReal (involSaddleRadius n)))

/-- The saddle radius is strictly positive for `n ≥ 1`. -/
lemma involSaddleRadius_pos_of_pos {n : ℕ} (hn : 0 < n) : 0 < involSaddleRadius n := by
  have hrnn : 0 ≤ involSaddleRadius n := involSaddleRadius_nonneg n
  have hA : involSaddleAReal (involSaddleRadius n) = (n : ℝ) := involSaddleAReal_radius n
  rcases hrnn.lt_or_eq with h | h
  · exact h
  · exfalso
    rw [← h] at hA
    simp only [involSaddleAReal] at hA
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    rw [← hA] at hnR
    simp at hnR

/-- The involution variance factor at the saddle is positive for `n ≥ 1`. -/
lemma involSaddleBReal_radius_pos_of_pos {n : ℕ} (hn : 0 < n) :
    0 < involSaddleBReal (involSaddleRadius n) := by
  have hr : 0 < involSaddleRadius n := involSaddleRadius_pos_of_pos hn
  unfold involSaddleBReal
  positivity

/-- The involution EGF is real on real input. -/
lemma involFun_real_on_real (r : ℝ) :
    involFun (r : ℂ) = (Real.exp (r + r ^ 2 / 2) : ℂ) := by
  unfold involFun
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring

/-- **Realification** of the abstract saddle scale to the Moser–Wyman real scale (`n ≥ 1`). -/
lemma invol_saddleScale_eq_ofReal_real_saddle {n : ℕ} (hn : 0 < n) :
    saddleScale involFun involSaddleRadius
        (fun n => involSaddleBReal (involSaddleRadius n)) n
      = (involRealSaddleScale n : ℂ) := by
  have hr : 0 < involSaddleRadius n := involSaddleRadius_pos_of_pos hn
  have hB : 0 < involSaddleBReal (involSaddleRadius n) := involSaddleBReal_radius_pos_of_pos hn
  have hsqrt : 0 < Real.sqrt (2 * Real.pi * involSaddleBReal (involSaddleRadius n)) :=
    Real.sqrt_pos.mpr (by positivity)
  unfold involRealSaddleScale saddleScale saddlePref saddlePrefAt
  rw [involFun_real_on_real]
  have hrC : ((involSaddleRadius n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hsqrtC :
      ((Real.sqrt (2 * Real.pi * involSaddleBReal (involSaddleRadius n)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hsqrt.ne'
  rw [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow]
  field_simp

/-- Eventual equality of the abstract complex scale and the real Moser–Wyman scale. -/
lemma invol_saddleScale_eventually_eq_ofReal_real_saddle :
    (fun n : ℕ =>
      saddleScale involFun involSaddleRadius
        (fun n => involSaddleBReal (involSaddleRadius n)) n)
      =ᶠ[atTop] (fun n : ℕ => (involRealSaddleScale n : ℂ)) := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact invol_saddleScale_eq_ofReal_real_saddle (by omega : 0 < n)

/-- **Moser–Wyman real saddle asymptotic for involutions**:
`I_n / n! ~ exp(r_n + r_n²/2) / (r_n^n √(2π (r_n + 2r_n²)))`, `r_n + r_n² = n`. -/
theorem involution_count_over_factorial_isEquivalent_real_saddle :
    (fun n : ℕ => involCoeffR n) ~[atTop] involRealSaddleScale := by
  rw [← ofReal_isEquivalent_iff]
  exact involution_count_over_factorial_isEquivalent_saddle.congr_right
    invol_saddleScale_eventually_eq_ofReal_real_saddle

end InvolutionHAdmissible
