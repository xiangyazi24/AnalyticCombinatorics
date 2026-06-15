import AnalyticCombinatorics.Ch8.SaddlePoint.BellHAdmissible
import AnalyticCombinatorics.Ch4.Analytic.RealAsymptotics

/-!
# Bell numbers: the classical Moser–Wyman real saddle asymptotic

`bell_number_over_factorial_isEquivalent_saddle` (BellHAdmissible) gives the H-admissible saddle
estimate `B_n/n! ~ saddleScale …` with a complex `saddleScale`.  This file realifies that abstract
scale to the recognizable Moser–Wyman formula

  `B_n / n! ~ exp(e^{r_n} − 1) / ( r_n^n · √(2π · r_n(r_n+1) e^{r_n}) )`,   `r_n e^{r_n} = n`,

where `r_n = bellSaddleRadius n` and `r_n(r_n+1)e^{r_n} = bellSaddleBReal (bellSaddleRadius n)`.
The content is an "unfold and realify" of `saddleScale` (all factors are real and positive for `n ≥ 1`),
transported back through `ofReal_isEquivalent_iff`.
-/

noncomputable section

open Filter Asymptotics
open scoped Topology Real

/-- The classical real Moser–Wyman Bell saddle scale. -/
noncomputable def bellRealSaddleScale (n : ℕ) : ℝ :=
  Real.exp (Real.exp (bellSaddleRadius n) - 1) /
    (bellSaddleRadius n ^ n *
      Real.sqrt (2 * Real.pi * bellSaddleBReal (bellSaddleRadius n)))

/-- The saddle radius is strictly positive for `n ≥ 1`. -/
lemma bellSaddleRadius_pos_of_pos {n : ℕ} (hn : 0 < n) : 0 < bellSaddleRadius n := by
  have hrnn : 0 ≤ bellSaddleRadius n := bellSaddleRadius_nonneg n
  have hA : bellSaddleAReal (bellSaddleRadius n) = (n : ℝ) := bellSaddleAReal_radius n
  rcases hrnn.lt_or_eq with h | h
  · exact h
  · exfalso
    rw [← h] at hA
    simp only [bellSaddleAReal] at hA
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    rw [← hA] at hnR
    simp at hnR

/-- The Bell variance factor at the saddle is positive for `n ≥ 1`. -/
lemma bellSaddleBReal_radius_pos_of_pos {n : ℕ} (hn : 0 < n) :
    0 < bellSaddleBReal (bellSaddleRadius n) := by
  have hr : 0 < bellSaddleRadius n := bellSaddleRadius_pos_of_pos hn
  unfold bellSaddleBReal
  positivity

/-- The analytic Bell function is real on real input. -/
lemma analyticBell_real_on_real (r : ℝ) :
    (fun z : ℂ => Complex.exp (Complex.exp z - 1)) (r : ℂ)
      = (Real.exp (Real.exp r - 1) : ℂ) := by
  push_cast
  rw [← Complex.ofReal_exp, ← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_exp]

/-- **Realification** of the abstract saddle scale to the Moser–Wyman real scale (`n ≥ 1`). -/
lemma bell_saddleScale_eq_ofReal_real_saddle {n : ℕ} (hn : 0 < n) :
    saddleScale
        (fun z : ℂ => Complex.exp (Complex.exp z - 1))
        bellSaddleRadius
        (fun n => bellSaddleBReal (bellSaddleRadius n))
        n
      = (bellRealSaddleScale n : ℂ) := by
  have hr : 0 < bellSaddleRadius n := bellSaddleRadius_pos_of_pos hn
  have hB : 0 < bellSaddleBReal (bellSaddleRadius n) := bellSaddleBReal_radius_pos_of_pos hn
  have hsqrt : 0 < Real.sqrt (2 * Real.pi * bellSaddleBReal (bellSaddleRadius n)) :=
    Real.sqrt_pos.mpr (by positivity)
  unfold bellRealSaddleScale saddleScale saddlePref saddlePrefAt
  rw [analyticBell_real_on_real]
  have hrC : ((bellSaddleRadius n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hsqrtC :
      ((Real.sqrt (2 * Real.pi * bellSaddleBReal (bellSaddleRadius n)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hsqrt.ne'
  rw [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow]
  field_simp

/-- Eventual equality of the abstract complex scale and the real Moser–Wyman scale. -/
lemma bell_saddleScale_eventually_eq_ofReal_real_saddle :
    (fun n : ℕ =>
      saddleScale
        (fun z : ℂ => Complex.exp (Complex.exp z - 1))
        bellSaddleRadius
        (fun n => bellSaddleBReal (bellSaddleRadius n))
        n)
      =ᶠ[atTop] (fun n : ℕ => (bellRealSaddleScale n : ℂ)) := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact bell_saddleScale_eq_ofReal_real_saddle (by omega : 0 < n)

/-- **Moser–Wyman real saddle asymptotic for Bell numbers**:
`B_n / n! ~ exp(e^{r_n} − 1) / (r_n^n √(2π r_n(r_n+1) e^{r_n}))`, `r_n e^{r_n} = n`. -/
theorem bell_number_over_factorial_isEquivalent_real_saddle :
    (fun n : ℕ => bellCoeffR n) ~[atTop] bellRealSaddleScale := by
  rw [← ofReal_isEquivalent_iff]
  exact bell_number_over_factorial_isEquivalent_saddle.congr_right
    bell_saddleScale_eventually_eq_ofReal_real_saddle
