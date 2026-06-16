import AnalyticCombinatorics.Ch8.SaddlePoint.Blocks3HAdmissible
import AnalyticCombinatorics.Ch4.Analytic.RealAsymptotics

/-!
# Set partitions into blocks of size ≤ 3: the Moser–Wyman real saddle asymptotic

`blocks3_count_over_factorial_isEquivalent_saddle` (Blocks3HAdmissible) gives the abstract H-admissible
saddle estimate for the number of set partitions of `[n]` into blocks of size 1, 2, or 3 (EGF
`exp(z + z²/2 + z³/6)`).  This file realifies the abstract scale to the Moser–Wyman formula

  `B₃(n) / n! ~ exp(r_n + r_n²/2 + r_n³/6) / ( r_n^n · √(2π · (r_n + 2r_n² + 3r_n³/2)) )`,
  `r_n + r_n² + r_n³/2 = n`.

"Unfold and realify" of `saddleScale`, mirroring `BellRealSaddle` / `InvolutionRealSaddle`.
-/

noncomputable section

open Filter Asymptotics
open scoped Topology Real

namespace Blocks3HAdmissible

/-- The Moser–Wyman real saddle scale for blocks-of-size-≤3 partitions. -/
noncomputable def blocks3RealSaddleScale (n : ℕ) : ℝ :=
  Real.exp (blocks3SaddleRadius n + (blocks3SaddleRadius n) ^ 2 / 2
      + (blocks3SaddleRadius n) ^ 3 / 6) /
    ((blocks3SaddleRadius n) ^ n *
      Real.sqrt (2 * Real.pi * blocks3SaddleBReal (blocks3SaddleRadius n)))

/-- The saddle radius is strictly positive for `n ≥ 1`. -/
lemma blocks3SaddleRadius_pos_of_pos {n : ℕ} (hn : 0 < n) : 0 < blocks3SaddleRadius n := by
  have hrnn : 0 ≤ blocks3SaddleRadius n := blocks3SaddleRadius_nonneg n
  have hA : blocks3SaddleAReal (blocks3SaddleRadius n) = (n : ℝ) := blocks3SaddleAReal_radius n
  rcases hrnn.lt_or_eq with h | h
  · exact h
  · exfalso
    rw [← h] at hA
    simp only [blocks3SaddleAReal] at hA
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    rw [← hA] at hnR
    simp at hnR

/-- The variance factor at the saddle is positive for `n ≥ 1`. -/
lemma blocks3SaddleBReal_radius_pos_of_pos {n : ℕ} (hn : 0 < n) :
    0 < blocks3SaddleBReal (blocks3SaddleRadius n) := by
  have hr : 0 < blocks3SaddleRadius n := blocks3SaddleRadius_pos_of_pos hn
  unfold blocks3SaddleBReal
  positivity

/-- The blocks-≤3 EGF is real on real input. -/
lemma blocks3Fun_real_on_real (r : ℝ) :
    blocks3Fun (r : ℂ) = (Real.exp (r + r ^ 2 / 2 + r ^ 3 / 6) : ℂ) := by
  unfold blocks3Fun
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring

/-- **Realification** of the abstract saddle scale (`n ≥ 1`). -/
lemma blocks3_saddleScale_eq_ofReal_real_saddle {n : ℕ} (hn : 0 < n) :
    saddleScale blocks3Fun blocks3SaddleRadius
        (fun n => blocks3SaddleBReal (blocks3SaddleRadius n)) n
      = (blocks3RealSaddleScale n : ℂ) := by
  have hr : 0 < blocks3SaddleRadius n := blocks3SaddleRadius_pos_of_pos hn
  have hB : 0 < blocks3SaddleBReal (blocks3SaddleRadius n) := blocks3SaddleBReal_radius_pos_of_pos hn
  have hsqrt : 0 < Real.sqrt (2 * Real.pi * blocks3SaddleBReal (blocks3SaddleRadius n)) :=
    Real.sqrt_pos.mpr (by positivity)
  unfold blocks3RealSaddleScale saddleScale saddlePref saddlePrefAt
  rw [blocks3Fun_real_on_real]
  have hrC : ((blocks3SaddleRadius n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hsqrtC :
      ((Real.sqrt (2 * Real.pi * blocks3SaddleBReal (blocks3SaddleRadius n)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hsqrt.ne'
  rw [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow]
  field_simp

/-- Eventual equality of the abstract complex scale and the real scale. -/
lemma blocks3_saddleScale_eventually_eq_ofReal_real_saddle :
    (fun n : ℕ =>
      saddleScale blocks3Fun blocks3SaddleRadius
        (fun n => blocks3SaddleBReal (blocks3SaddleRadius n)) n)
      =ᶠ[atTop] (fun n : ℕ => (blocks3RealSaddleScale n : ℂ)) := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact blocks3_saddleScale_eq_ofReal_real_saddle (by omega : 0 < n)

/-- **Moser–Wyman real saddle asymptotic for blocks-of-size-≤3 set partitions**:
`B₃(n)/n! ~ exp(r_n + r_n²/2 + r_n³/6) / (r_n^n √(2π (r_n + 2r_n² + 3r_n³/2)))`,
`r_n + r_n² + r_n³/2 = n`. -/
theorem blocks3_count_over_factorial_isEquivalent_real_saddle :
    (fun n : ℕ => blocks3CoeffR n) ~[atTop] blocks3RealSaddleScale := by
  rw [← ofReal_isEquivalent_iff]
  exact blocks3_count_over_factorial_isEquivalent_saddle.congr_right
    blocks3_saddleScale_eventually_eq_ofReal_real_saddle

end Blocks3HAdmissible
