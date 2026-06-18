import AnalyticCombinatorics.Ch8.SaddlePoint.GaussianMoments

/-!
# Second-order saddle core definitions

This file defines the universal Gaussian correction polynomial and the scalar
second-order correction appearing after integrating its even moments.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval

noncomputable section

/-- Second-order local polynomial in the scaled variable `x`. -/
def saddleSecondPoly (b b3 b4 : ℝ → ℝ) (r x : ℝ) : ℂ :=
  1
    - Complex.I * ((b3 r : ℂ) / (6 * (Real.sqrt (b r) : ℂ) ^ 3)) * (x : ℂ) ^ 3
    + ((b4 r : ℂ) / (24 * (b r : ℂ) ^ 2)) * (x : ℂ) ^ 4
    - (((b3 r) ^ 2 : ℝ) : ℂ) / (72 * (b r : ℂ) ^ 3) * (x : ℂ) ^ 6

/-- The scalar second-order saddle correction. -/
def saddleCorrection (b b3 b4 : ℝ → ℝ) (r : ℝ) : ℝ :=
  b4 r / (8 * (b r) ^ 2) - 5 * (b3 r) ^ 2 / (24 * (b r) ^ 3)

/--
Robust absolute correction scale.  This is the scale used before specializing
to the signed correction, so cancellation in `saddleCorrection` does not hide
the true error size.
-/
def saddleCorrectionScale (b b3 b4 : ℝ → ℝ) (r : ℝ) : ℝ :=
  |b4 r| / (b r) ^ 2 + (b3 r) ^ 2 / (b r) ^ 3

@[simp] lemma saddleSecondPoly_apply (b b3 b4 : ℝ → ℝ) (r x : ℝ) :
    saddleSecondPoly b b3 b4 r x =
      1
        - Complex.I * ((b3 r : ℂ) / (6 * (Real.sqrt (b r) : ℂ) ^ 3)) * (x : ℂ) ^ 3
        + ((b4 r : ℂ) / (24 * (b r : ℂ) ^ 2)) * (x : ℂ) ^ 4
        - (((b3 r) ^ 2 : ℝ) : ℂ) / (72 * (b r : ℂ) ^ 3) * (x : ℂ) ^ 6 := rfl

@[simp] lemma saddleCorrection_apply (b b3 b4 : ℝ → ℝ) (r : ℝ) :
    saddleCorrection b b3 b4 r =
      b4 r / (8 * (b r) ^ 2) - 5 * (b3 r) ^ 2 / (24 * (b r) ^ 3) := rfl

@[simp] lemma saddleCorrectionScale_apply (b b3 b4 : ℝ → ℝ) (r : ℝ) :
    saddleCorrectionScale b b3 b4 r =
      |b4 r| / (b r) ^ 2 + (b3 r) ^ 2 / (b r) ^ 3 := rfl

lemma saddleSecondPoly_quarticCoeff_norm_le_scale
    {b b3 b4 : ℝ → ℝ} {r : ℝ} (hb : 0 < b r) :
    ‖(b4 r : ℂ) / (24 * (b r : ℂ) ^ 2)‖ ≤
      (1 / 24 : ℝ) * saddleCorrectionScale b b3 b4 r := by
  have hb2pos : 0 < (b r) ^ 2 := sq_pos_of_pos hb
  have hb3nonneg : 0 ≤ (b3 r) ^ 2 / (b r) ^ 3 := by
    exact div_nonneg (sq_nonneg _) (by positivity)
  calc
    ‖(b4 r : ℂ) / (24 * (b r : ℂ) ^ 2)‖
        = |b4 r| / (24 * (b r) ^ 2) := by
          simp [norm_pow, Real.norm_eq_abs, abs_of_pos hb]
    _ = (1 / 24 : ℝ) * (|b4 r| / (b r) ^ 2) := by ring
    _ ≤ (1 / 24 : ℝ) * (|b4 r| / (b r) ^ 2 + (b3 r) ^ 2 / (b r) ^ 3) := by
          exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hb3nonneg)
            (by norm_num)
    _ = (1 / 24 : ℝ) * saddleCorrectionScale b b3 b4 r := by rfl

lemma saddleSecondPoly_sexticCoeff_norm_le_scale
    {b b3 b4 : ℝ → ℝ} {r : ℝ} (hb : 0 < b r) :
    ‖(((b3 r) ^ 2 : ℝ) : ℂ) / (72 * (b r : ℂ) ^ 3)‖ ≤
      (1 / 72 : ℝ) * saddleCorrectionScale b b3 b4 r := by
  have hb2nonneg : 0 ≤ |b4 r| / (b r) ^ 2 := by
    exact div_nonneg (abs_nonneg _) (sq_nonneg _)
  calc
    ‖(((b3 r) ^ 2 : ℝ) : ℂ) / (72 * (b r : ℂ) ^ 3)‖
        = (b3 r) ^ 2 / (72 * (b r) ^ 3) := by
          simp [norm_pow, Real.norm_eq_abs, abs_of_pos hb]
    _ = (1 / 72 : ℝ) * ((b3 r) ^ 2 / (b r) ^ 3) := by ring
    _ ≤ (1 / 72 : ℝ) * (|b4 r| / (b r) ^ 2 + (b3 r) ^ 2 / (b r) ^ 3) := by
          exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hb2nonneg)
            (by norm_num)
    _ = (1 / 72 : ℝ) * saddleCorrectionScale b b3 b4 r := by rfl

private lemma gaussian_weighted_integrable_zero :
    Integrable (fun x : ℝ => Real.exp (-(x ^ 2) / 2)) := by
  simpa [show (fun x : ℝ => Real.exp (-(x ^ 2) / 2)) =
      (fun x : ℝ => Real.exp (-(1 / 2 : ℝ) * x ^ 2)) by
        funext x
        ring_nf] using
    (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2))

private lemma gaussian_weighted_integrable_three :
    Integrable (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * x ^ 3) := by
  simpa [show (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * x ^ 3) =
      (fun x : ℝ => x ^ 3 * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) by
        funext x
        ring_nf] using
    (integrable_rpow_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (-1 : ℝ) < 3))

private lemma gaussian_weighted_integrable_four :
    Integrable (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * x ^ 4) := by
  simpa [show (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * x ^ 4) =
      (fun x : ℝ => x ^ 4 * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) by
        funext x
        ring_nf] using
    (integrable_rpow_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (-1 : ℝ) < 4))

private lemma gaussian_weighted_integrable_six :
    Integrable (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * x ^ 6) := by
  simpa [show (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * x ^ 6) =
      (fun x : ℝ => x ^ 6 * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) by
        funext x
        ring_nf] using
    (integrable_rpow_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (-1 : ℝ) < 6))

private lemma gaussian_complex_integrable_zero :
    Integrable (fun x : ℝ => Complex.exp (-(x ^ 2) / 2)) := by
  simpa using (gaussian_weighted_integrable_zero.ofReal (𝕜 := ℂ))

private lemma gaussian_complex_integrable_three :
    Integrable (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 3) := by
  simpa using (gaussian_weighted_integrable_three.ofReal (𝕜 := ℂ))

private lemma gaussian_complex_integrable_four :
    Integrable (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 4) := by
  simpa using (gaussian_weighted_integrable_four.ofReal (𝕜 := ℂ))

private lemma gaussian_complex_integrable_six :
    Integrable (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6) := by
  simpa using (gaussian_weighted_integrable_six.ofReal (𝕜 := ℂ))

private lemma gaussian_complex_weighted_moment_three :
    (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 3) = (0 : ℂ) := by
  let g : ℝ → ℂ := fun x => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 3
  have hcomp : (∫ x : ℝ, g (-x)) = ∫ x : ℝ, g x := by
    exact (Measure.measurePreserving_neg (volume : Measure ℝ)).integral_comp
      (Homeomorph.neg ℝ).measurableEmbedding g
  have hodd : (fun x : ℝ => g (-x)) = fun x : ℝ => -g x := by
    funext x
    simp [g]
    ring
  rw [hodd] at hcomp
  rw [integral_neg] at hcomp
  have hzero : (∫ x : ℝ, g x) = -(∫ x : ℝ, g x) := hcomp.symm
  have htwo : (2 : ℂ) * (∫ x : ℝ, g x) = 0 := by
    calc
      (2 : ℂ) * (∫ x : ℝ, g x) =
          (∫ x : ℝ, g x) + (∫ x : ℝ, g x) := by ring
      _ = -(∫ x : ℝ, g x) + (∫ x : ℝ, g x) := by
            nth_rw 1 [hzero]
      _ = 0 := by ring
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num : (2 : ℂ) ≠ 0)

/-- The odd cubic Gaussian moment vanishes on every symmetric window. -/
lemma gaussian_window_weighted_moment_three_eq_zero (L : ℝ) :
    (∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 3) = 0 := by
  let g : ℝ → ℂ := fun x => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 3
  have hcomp : (∫ x in -L..L, g (-x)) = ∫ x in -L..L, g x := by
    simpa only [neg_neg] using
      (intervalIntegral.integral_comp_neg (f := g) (a := -L) (b := L))
  have hodd : (fun x : ℝ => g (-x)) = fun x : ℝ => -g x := by
    funext x
    simp [g]
    ring
  rw [hodd] at hcomp
  rw [intervalIntegral.integral_neg] at hcomp
  have hzero : (∫ x in -L..L, g x) = -(∫ x in -L..L, g x) := hcomp.symm
  have htwo : (2 : ℂ) * (∫ x in -L..L, g x) = 0 := by
    calc
      (2 : ℂ) * (∫ x in -L..L, g x) =
          (∫ x in -L..L, g x) + (∫ x in -L..L, g x) := by ring
      _ = -(∫ x in -L..L, g x) + (∫ x in -L..L, g x) := by
            nth_rw 1 [hzero]
      _ = 0 := by ring
  simpa [g] using (mul_eq_zero.mp htwo).resolve_left (by norm_num : (2 : ℂ) ≠ 0)

private lemma gaussian_complex_weighted_moment_four :
    (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 4) =
      (3 * Real.sqrt (2 * Real.pi) : ℂ) := by
  rw [show (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 4) =
      (fun x : ℝ => ((Real.exp (-(x ^ 2) / 2) * x ^ 4 : ℝ) : ℂ)) by
        funext x
        simp]
  exact_mod_cast gaussian_weighted_moment_four

private lemma gaussian_complex_weighted_moment_six :
    (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6) =
      (15 * Real.sqrt (2 * Real.pi) : ℂ) := by
  rw [show (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6) =
      (fun x : ℝ => ((Real.exp (-(x ^ 2) / 2) * x ^ 6 : ℝ) : ℂ)) by
        funext x
        simp]
  exact_mod_cast gaussian_weighted_moment_six

/--
Integrating the universal second-order polynomial against the Gaussian produces
exactly the scalar saddle correction.  The odd cubic term vanishes, while the
quartic and sextic terms use the `3` and `15` Gaussian moments.
-/
theorem gaussian_integral_saddleSecondPoly (b b3 b4 : ℝ → ℝ) (r : ℝ) :
    (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * saddleSecondPoly b b3 b4 r x) =
      (Real.sqrt (2 * Real.pi) : ℂ) *
        (1 + (saddleCorrection b b3 b4 r : ℂ)) := by
  let A : ℂ := Complex.I * ((b3 r : ℂ) / (6 * (Real.sqrt (b r) : ℂ) ^ 3))
  let D : ℂ := (b4 r : ℂ) / (24 * (b r : ℂ) ^ 2)
  let E : ℂ := (((b3 r) ^ 2 : ℝ) : ℂ) / (72 * (b r : ℂ) ^ 3)
  let F0 : ℝ → ℂ := fun x => Complex.exp (-(x ^ 2) / 2)
  let F3 : ℝ → ℂ := fun x => A * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 3)
  let F4 : ℝ → ℂ := fun x => D * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 4)
  let F6 : ℝ → ℂ := fun x => E * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6)
  have hpoly :
      (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * saddleSecondPoly b b3 b4 r x) =
        fun x : ℝ => (F0 - F3 + F4 - F6) x := by
    funext x
    simp [F0, F3, F4, F6, saddleSecondPoly, A, D, E]
    ring
  rw [hpoly]
  have hF0 : Integrable F0 := by
    simpa [F0] using gaussian_complex_integrable_zero
  have hF3 : Integrable F3 := by
    simpa [F3] using gaussian_complex_integrable_three.const_mul A
  have hF4 : Integrable F4 := by
    simpa [F4] using gaussian_complex_integrable_four.const_mul D
  have hF6 : Integrable F6 := by
    simpa [F6] using gaussian_complex_integrable_six.const_mul E
  have hF03 : Integrable (fun x : ℝ => F0 x - F3 x) := hF0.sub hF3
  have hF034 : Integrable (fun x : ℝ => F0 x - F3 x + F4 x) := hF03.add hF4
  simp only [Pi.sub_apply, Pi.add_apply]
  rw [integral_sub hF034 hF6]
  rw [integral_add hF03 hF4]
  rw [integral_sub hF0 hF3]
  simp only [F0, F3, F4, F6]
  have hAeval :
      (∫ x : ℝ, A * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 3)) =
        A * ∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 3 :=
    integral_const_mul A
      (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 3)
  have hDeval :
      (∫ x : ℝ, D * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 4)) =
        D * ∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 4 :=
    integral_const_mul D
      (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 4)
  have hEeval :
      (∫ x : ℝ, E * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6)) =
        E * ∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6 :=
    integral_const_mul E
      (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6)
  rw [hAeval, hDeval, hEeval]
  rw [gaussian_integral_half, gaussian_complex_weighted_moment_three,
    gaussian_complex_weighted_moment_four, gaussian_complex_weighted_moment_six]
  simp [A, D, E, saddleCorrection]
  ring_nf

/-- The scalar correction is exactly the normalized quartic and sextic Gaussian moments. -/
theorem saddleCorrection_eq_gaussian_even_moments (b b3 b4 : ℝ → ℝ) (r : ℝ) :
    (saddleCorrection b b3 b4 r : ℂ) =
      (1 / Real.sqrt (2 * Real.pi) : ℂ) *
        (((b4 r : ℂ) / (24 * (b r : ℂ) ^ 2)) *
            (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 4) -
          ((((b3 r) ^ 2 : ℝ) : ℂ) / (72 * (b r : ℂ) ^ 3)) *
            (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6)) := by
  rw [gaussian_complex_weighted_moment_four, gaussian_complex_weighted_moment_six]
  simp [saddleCorrection]
  have hsqrtπ_ne : (Real.sqrt Real.pi : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hsqrt2_ne : (Real.sqrt (2 : ℝ) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  field_simp [hsqrtπ_ne, hsqrt2_ne]
  ring_nf

/--
Symmetric-window version of the polynomial expansion.  The cubic contribution
vanishes exactly on `[-L,L]`.
-/
theorem gaussian_window_integral_saddleSecondPoly
    (b b3 b4 : ℝ → ℝ) (r L : ℝ) :
    (∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) *
        saddleSecondPoly b b3 b4 r x) =
      (∫ x in -L..L, Complex.exp (-(x ^ 2) / 2)) +
        ((b4 r : ℂ) / (24 * (b r : ℂ) ^ 2)) *
          (∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 4) -
        ((((b3 r) ^ 2 : ℝ) : ℂ) / (72 * (b r : ℂ) ^ 3)) *
          (∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6) := by
  let A : ℂ := Complex.I * ((b3 r : ℂ) / (6 * (Real.sqrt (b r) : ℂ) ^ 3))
  let D : ℂ := (b4 r : ℂ) / (24 * (b r : ℂ) ^ 2)
  let E : ℂ := (((b3 r) ^ 2 : ℝ) : ℂ) / (72 * (b r : ℂ) ^ 3)
  let F0 : ℝ → ℂ := fun x => Complex.exp (-(x ^ 2) / 2)
  let F3 : ℝ → ℂ := fun x => A * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 3)
  let F4 : ℝ → ℂ := fun x => D * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 4)
  let F6 : ℝ → ℂ := fun x => E * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6)
  have hpoly :
      (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * saddleSecondPoly b b3 b4 r x) =
        fun x : ℝ => (F0 - F3 + F4 - F6) x := by
    funext x
    simp [F0, F3, F4, F6, saddleSecondPoly, A, D, E]
    ring
  rw [hpoly]
  have hF0 : IntervalIntegrable F0 volume (-L) L := by
    have hcont : Continuous F0 := by
      unfold F0
      fun_prop
    exact hcont.intervalIntegrable _ _
  have hF3 : IntervalIntegrable F3 volume (-L) L := by
    have hcont : Continuous F3 := by
      unfold F3
      fun_prop
    exact hcont.intervalIntegrable _ _
  have hF4 : IntervalIntegrable F4 volume (-L) L := by
    have hcont : Continuous F4 := by
      unfold F4
      fun_prop
    exact hcont.intervalIntegrable _ _
  have hF6 : IntervalIntegrable F6 volume (-L) L := by
    have hcont : Continuous F6 := by
      unfold F6
      fun_prop
    exact hcont.intervalIntegrable _ _
  have hF03 : IntervalIntegrable (fun x : ℝ => F0 x - F3 x) volume (-L) L := hF0.sub hF3
  have hF034 : IntervalIntegrable (fun x : ℝ => F0 x - F3 x + F4 x) volume (-L) L :=
    hF03.add hF4
  simp only [Pi.sub_apply, Pi.add_apply]
  rw [intervalIntegral.integral_sub hF034 hF6]
  rw [intervalIntegral.integral_add hF03 hF4]
  rw [intervalIntegral.integral_sub hF0 hF3]
  simp only [F0, F3, F4, F6]
  have hAeval :
      (∫ x in -L..L, A * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 3)) =
        A * ∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 3 := by
    exact intervalIntegral.integral_const_mul A
      (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 3)
  have hDeval :
      (∫ x in -L..L, D * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 4)) =
        D * ∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 4 := by
    exact intervalIntegral.integral_const_mul D
      (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 4)
  have hEeval :
      (∫ x in -L..L, E * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6)) =
        E * ∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6 := by
    exact intervalIntegral.integral_const_mul E
      (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6)
  rw [hAeval, hDeval, hEeval, gaussian_window_weighted_moment_three_eq_zero]
  simp [A, D, E]

/-- Expanding symmetric windows exhaust an integrable function on the line. -/
lemma intervalIntegral_tendsto_integral_symmetric
    {g : ℝ → ℂ} (hg : Integrable g) {L : ℕ → ℝ}
    (hL : Tendsto L atTop atTop) :
    Tendsto (fun n : ℕ => ∫ x in -(L n)..(L n), g x)
      atTop (𝓝 (∫ x : ℝ, g x)) := by
  simpa using
    (intervalIntegral_tendsto_integral (μ := volume) hg
      (tendsto_neg_atTop_atBot.comp hL) hL)

/-- Fourth weighted Gaussian windows converge to the full fourth moment. -/
lemma gaussian_window_weighted_moment_four_tendsto
    {L : ℕ → ℝ} (hL : Tendsto L atTop atTop) :
    Tendsto
      (fun n : ℕ =>
        ∫ x in -(L n)..(L n),
          Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 4)
      atTop
      (𝓝 (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 4)) :=
  intervalIntegral_tendsto_integral_symmetric gaussian_complex_integrable_four hL

/-- Sixth weighted Gaussian windows converge to the full sixth moment. -/
lemma gaussian_window_weighted_moment_six_tendsto
    {L : ℕ → ℝ} (hL : Tendsto L atTop atTop) :
    Tendsto
      (fun n : ℕ =>
        ∫ x in -(L n)..(L n),
          Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6)
      atTop
      (𝓝 (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6)) :=
  intervalIntegral_tendsto_integral_symmetric gaussian_complex_integrable_six hL

/-- A crude one-sided Gaussian tail bound, enough for relative saddle-window estimates. -/
lemma gaussian_tail_Ioi_le_exp {L : ℝ} (hL : 1 ≤ L) :
    (∫ x in Set.Ioi L, Real.exp (-(x ^ 2) / 2)) ≤
      Real.exp (-(L ^ 2) / 2) := by
  have hderiv : ∀ x ∈ Set.Ici L,
      HasDerivAt (fun y : ℝ => -Real.exp (-(y ^ 2) / 2))
        (x * Real.exp (-(x ^ 2) / 2)) x := by
    intro x _hx
    have h1 : HasDerivAt (fun y : ℝ => -(y ^ 2) / 2) (-x) x := by
      convert ((hasDerivAt_pow 2 x).neg.div_const 2) using 1
      ring
    have h2 := h1.exp.neg
    convert h2 using 1
    ring
  have hint : IntegrableOn (fun x : ℝ => x * Real.exp (-(x ^ 2) / 2)) (Set.Ioi L) := by
    have hbase : Integrable (fun x : ℝ => x * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) :=
      integrable_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)
    convert hbase.integrableOn using 1
    funext x
    ring_nf
  have htop : Tendsto (fun y : ℝ => -Real.exp (-(y ^ 2) / 2)) atTop (𝓝 0) := by
    have hsq : Tendsto (fun y : ℝ => -(y ^ 2) / 2) atTop atBot := by
      have hpow : Tendsto (fun y : ℝ => y ^ 2) atTop atTop :=
        tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
      have hmul : Tendsto (fun y : ℝ => (-(1 / 2 : ℝ)) * y ^ 2) atTop atBot :=
        (tendsto_const_mul_atBot_of_neg (by norm_num : (-(1 / 2 : ℝ)) < 0)).mpr hpow
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
    have hexp : Tendsto (fun y : ℝ => Real.exp (-(y ^ 2) / 2)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp hsq
    simpa using hexp.neg
  have hxeq : (∫ x in Set.Ioi L, x * Real.exp (-(x ^ 2) / 2)) =
      Real.exp (-(L ^ 2) / 2) := by
    convert integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint htop using 1
    ring
  have hleftint : IntegrableOn (fun x : ℝ => Real.exp (-(x ^ 2) / 2)) (Set.Ioi L) := by
    have hbase : Integrable (fun x : ℝ => Real.exp (-(1 / 2 : ℝ) * x ^ 2)) :=
      integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)
    convert hbase.integrableOn using 1
    funext x
    ring_nf
  have hmono : (∫ x in Set.Ioi L, Real.exp (-(x ^ 2) / 2)) ≤
      ∫ x in Set.Ioi L, x * Real.exp (-(x ^ 2) / 2) := by
    refine setIntegral_mono_on hleftint hint measurableSet_Ioi ?_
    intro x hx
    have hxL : L < x := hx
    have hx1 : 1 ≤ x := le_trans hL (le_of_lt hxL)
    have hnon : 0 ≤ Real.exp (-(x ^ 2) / 2) := (Real.exp_pos _).le
    calc
      Real.exp (-(x ^ 2) / 2) = 1 * Real.exp (-(x ^ 2) / 2) := by simp
      _ ≤ x * Real.exp (-(x ^ 2) / 2) :=
            mul_le_mul_of_nonneg_right hx1 hnon
  simpa [hxeq] using hmono

/--
The normalized zeroth Gaussian window differs from `1` by at most a constant
times the one-sided Gaussian boundary exponential.
-/
lemma gaussian_window_zero_error_norm_le_exp {L : ℝ} (hL : 1 ≤ L) :
    ‖(1 / Real.sqrt (2 * Real.pi) : ℂ) *
        (∫ x in -L..L, Complex.exp (-(x ^ 2) / 2)) - 1‖
      ≤ (2 / Real.sqrt (2 * Real.pi)) * Real.exp (-(L ^ 2) / 2) := by
  let g : ℝ → ℂ := fun x => Complex.exp (-(x ^ 2) / 2)
  let tail : ℂ := ∫ x in Set.Ioi L, g x
  let leftTail : ℂ := ∫ x in Set.Iic (-L), g x
  let window : ℂ := ∫ x in -L..L, g x
  let invG : ℂ := (1 / Real.sqrt (2 * Real.pi) : ℂ)
  have hLnonneg : 0 ≤ L := le_trans zero_le_one hL
  have hg : Integrable g := by
    simpa [g] using gaussian_complex_integrable_zero
  have hleftInt : IntegrableOn g (Set.Iic (-L)) := hg.integrableOn
  have hrightFromLeft : IntegrableOn g (Set.Ioi (-L)) := hg.integrableOn
  have hrightInt : IntegrableOn g (Set.Ioi L) := hg.integrableOn
  have hsplitFull :
      leftTail + (∫ x in Set.Ioi (-L), g x) = ∫ x : ℝ, g x := by
    simpa [leftTail] using
      (intervalIntegral.integral_Iic_add_Ioi (f := g) (b := -L) hleftInt hrightFromLeft)
  have hsplitRight :
      window + tail = ∫ x in Set.Ioi (-L), g x := by
    simpa [window, tail] using
      (intervalIntegral.integral_interval_add_Ioi
        (f := g) (a := -L) (b := L) hrightFromLeft hrightInt)
  have hfull :
      (∫ x : ℝ, g x) = leftTail + window + tail := by
    calc
      (∫ x : ℝ, g x) = leftTail + (∫ x in Set.Ioi (-L), g x) := hsplitFull.symm
      _ = leftTail + (window + tail) := by rw [← hsplitRight]
      _ = leftTail + window + tail := by ring
  have hsqrt_pos : 0 < Real.sqrt (2 * Real.pi) := by positivity
  have hinv_full : invG * (∫ x : ℝ, g x) = 1 := by
    rw [gaussian_integral_half]
    change (1 / (Real.sqrt (2 * Real.pi) : ℂ)) *
        (Real.sqrt (2 * Real.pi) : ℂ) = 1
    field_simp [Complex.ofReal_ne_zero.mpr hsqrt_pos.ne']
  have hdiff :
      invG * window - 1 = -invG * (leftTail + tail) := by
    rw [← hinv_full, hfull]
    ring
  have hrightNorm :
      ‖tail‖ ≤ Real.exp (-(L ^ 2) / 2) := by
    calc
      ‖tail‖ ≤ ∫ x in Set.Ioi L, ‖g x‖ := by
        simpa [tail] using
          (norm_integral_le_integral_norm
            (f := fun x : ℝ => g x) (μ := volume.restrict (Set.Ioi L)))
      _ = ∫ x in Set.Ioi L, Real.exp (-(x ^ 2) / 2) := by
        apply integral_congr_ae
        refine ae_of_all _ ?_
        intro x
        simp [g, Complex.norm_exp, sq]
      _ ≤ Real.exp (-(L ^ 2) / 2) := gaussian_tail_Ioi_le_exp hL
  have hleftEq : leftTail = tail := by
    have hcomp :
        (∫ x in Set.Iic (-L), g (-x)) = ∫ x in Set.Ioi L, g x := by
      simpa only [neg_neg] using (integral_comp_neg_Iic (c := -L) (f := g))
    have heven :
        (∫ x in Set.Iic (-L), g (-x)) = ∫ x in Set.Iic (-L), g x := by
      apply setIntegral_congr_fun measurableSet_Iic
      intro x _hx
      simp [g]
    simpa [leftTail, tail] using heven.symm.trans hcomp
  have hleftNorm :
      ‖leftTail‖ ≤ Real.exp (-(L ^ 2) / 2) := by
    simpa [hleftEq] using hrightNorm
  calc
    ‖invG * window - 1‖ = ‖-invG * (leftTail + tail)‖ := by rw [hdiff]
    _ ≤ ‖invG‖ * (‖leftTail‖ + ‖tail‖) := by
      rw [norm_mul, norm_neg]
      exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
    _ ≤ ‖invG‖ *
        (Real.exp (-(L ^ 2) / 2) + Real.exp (-(L ^ 2) / 2)) := by
      exact mul_le_mul_of_nonneg_left (add_le_add hleftNorm hrightNorm) (norm_nonneg _)
    _ = (2 / Real.sqrt (2 * Real.pi)) * Real.exp (-(L ^ 2) / 2) := by
      have hinv_norm : ‖invG‖ = 1 / Real.sqrt (2 * Real.pi) := by
        dsimp [invG]
        rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hsqrt_pos]
      rw [hinv_norm]
      ring
