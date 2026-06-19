import AnalyticCombinatorics.Ch8.SaddlePoint.SecondOrderCore

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-!
# Third-order saddle core definitions

This file extends the universal second-order Gaussian correction polynomial by
the order-`b^{-2}` terms in the Hayman saddle expansion.
-/

open Complex Filter Asymptotics MeasureTheory ProbabilityTheory
open scoped Topology Real NNReal ENNReal Interval

noncomputable section

/-- Third-order local polynomial in the scaled variable `x`. -/
def saddleThirdPoly (b b3 b4 b5 b6 : ℝ → ℝ) (r x : ℝ) : ℂ :=
  saddleSecondPoly b b3 b4 r x
    + Complex.I * ((b5 r : ℂ) / (120 * (Real.sqrt (b r) : ℂ) ^ 5)) * (x : ℂ) ^ 5
    - ((b6 r : ℂ) / (720 * (b r : ℂ) ^ 3)) * (x : ℂ) ^ 6
    - Complex.I * (((b3 r * b4 r : ℝ) : ℂ) /
        (144 * (Real.sqrt (b r) : ℂ) ^ 3 * (b r : ℂ) ^ 2)) * (x : ℂ) ^ 7
    + (((b3 r * b5 r : ℝ) : ℂ) / (720 * (b r : ℂ) ^ 4)) * (x : ℂ) ^ 8
    + ((((b4 r) ^ 2 : ℝ) : ℂ) / (1152 * (b r : ℂ) ^ 4)) * (x : ℂ) ^ 8
    + Complex.I * ((((b3 r) ^ 3 : ℝ) : ℂ) /
        (1296 * (Real.sqrt (b r) : ℂ) ^ 9)) * (x : ℂ) ^ 9
    - (((((b3 r) ^ 2 * b4 r : ℝ) : ℂ) / (1728 * (b r : ℂ) ^ 5)) *
        (x : ℂ) ^ 10)
    + ((((b3 r) ^ 4 : ℝ) : ℂ) / (31104 * (b r : ℂ) ^ 6)) * (x : ℂ) ^ 12

/-- The scalar third-order saddle correction `δ₂`. -/
def saddleThirdCorrection (b b3 b4 b5 b6 : ℝ → ℝ) (r : ℝ) : ℝ :=
  - b6 r / (48 * (b r) ^ 3)
    + 7 * b3 r * b5 r / (48 * (b r) ^ 4)
    + 35 * (b4 r) ^ 2 / (384 * (b r) ^ 4)
    - 35 * (b3 r) ^ 2 * b4 r / (64 * (b r) ^ 5)
    + 385 * (b3 r) ^ 4 / (1152 * (b r) ^ 6)

/--
Robust coefficient scale for the third-order polynomial.  It includes the
second-order coefficient scale because window truncation errors multiply every
nonconstant coefficient of the polynomial.
-/
def saddleThirdCorrectionScale (b b3 b4 b5 b6 : ℝ → ℝ) (r : ℝ) : ℝ :=
  saddleCorrectionScale b b3 b4 r
    + |b6 r| / (b r) ^ 3
    + |b3 r * b5 r| / (b r) ^ 4
    + (b4 r) ^ 2 / (b r) ^ 4
    + (b3 r) ^ 2 * |b4 r| / (b r) ^ 5
    + (b3 r) ^ 4 / (b r) ^ 6

@[simp] lemma saddleThirdPoly_apply (b b3 b4 b5 b6 : ℝ → ℝ) (r x : ℝ) :
    saddleThirdPoly b b3 b4 b5 b6 r x =
      saddleSecondPoly b b3 b4 r x
        + Complex.I * ((b5 r : ℂ) / (120 * (Real.sqrt (b r) : ℂ) ^ 5)) *
            (x : ℂ) ^ 5
        - ((b6 r : ℂ) / (720 * (b r : ℂ) ^ 3)) * (x : ℂ) ^ 6
        - Complex.I * (((b3 r * b4 r : ℝ) : ℂ) /
            (144 * (Real.sqrt (b r) : ℂ) ^ 3 * (b r : ℂ) ^ 2)) *
            (x : ℂ) ^ 7
        + (((b3 r * b5 r : ℝ) : ℂ) / (720 * (b r : ℂ) ^ 4)) *
            (x : ℂ) ^ 8
        + ((((b4 r) ^ 2 : ℝ) : ℂ) / (1152 * (b r : ℂ) ^ 4)) *
            (x : ℂ) ^ 8
        + Complex.I * ((((b3 r) ^ 3 : ℝ) : ℂ) /
            (1296 * (Real.sqrt (b r) : ℂ) ^ 9)) * (x : ℂ) ^ 9
        - (((((b3 r) ^ 2 * b4 r : ℝ) : ℂ) / (1728 * (b r : ℂ) ^ 5)) *
            (x : ℂ) ^ 10)
        + ((((b3 r) ^ 4 : ℝ) : ℂ) / (31104 * (b r : ℂ) ^ 6)) *
            (x : ℂ) ^ 12 := rfl

@[simp] lemma saddleThirdCorrection_apply (b b3 b4 b5 b6 : ℝ → ℝ) (r : ℝ) :
    saddleThirdCorrection b b3 b4 b5 b6 r =
      - b6 r / (48 * (b r) ^ 3)
        + 7 * b3 r * b5 r / (48 * (b r) ^ 4)
        + 35 * (b4 r) ^ 2 / (384 * (b r) ^ 4)
        - 35 * (b3 r) ^ 2 * b4 r / (64 * (b r) ^ 5)
        + 385 * (b3 r) ^ 4 / (1152 * (b r) ^ 6) := rfl

@[simp] lemma saddleThirdCorrectionScale_apply (b b3 b4 b5 b6 : ℝ → ℝ) (r : ℝ) :
    saddleThirdCorrectionScale b b3 b4 b5 b6 r =
      saddleCorrectionScale b b3 b4 r
        + |b6 r| / (b r) ^ 3
        + |b3 r * b5 r| / (b r) ^ 4
        + (b4 r) ^ 2 / (b r) ^ 4
        + (b3 r) ^ 2 * |b4 r| / (b r) ^ 5
        + (b3 r) ^ 4 / (b r) ^ 6 := rfl

private lemma saddleThirdCorrectionScale_nonneg
    {b b3 b4 b5 b6 : ℝ → ℝ} {r : ℝ} (hb : 0 < b r) :
    0 ≤ saddleThirdCorrectionScale b b3 b4 b5 b6 r := by
  dsimp [saddleThirdCorrectionScale, saddleCorrectionScale]
  positivity

private lemma saddleCorrectionScale_le_saddleThirdCorrectionScale
    {b b3 b4 b5 b6 : ℝ → ℝ} {r : ℝ} (hb : 0 < b r) :
    saddleCorrectionScale b b3 b4 r ≤
      saddleThirdCorrectionScale b b3 b4 b5 b6 r := by
  dsimp [saddleThirdCorrectionScale]
  have h1 : 0 ≤ |b6 r| / (b r) ^ 3 := by positivity
  have h2 : 0 ≤ |b3 r * b5 r| / (b r) ^ 4 := by positivity
  have h3 : 0 ≤ (b4 r) ^ 2 / (b r) ^ 4 := by positivity
  have h4 : 0 ≤ (b3 r) ^ 2 * |b4 r| / (b r) ^ 5 := by positivity
  have h5 : 0 ≤ (b3 r) ^ 4 / (b r) ^ 6 := by positivity
  nlinarith

private lemma saddleThirdScale_term_b6_le
    {b b3 b4 b5 b6 : ℝ → ℝ} {r : ℝ} (hb : 0 < b r) :
    |b6 r| / (b r) ^ 3 ≤ saddleThirdCorrectionScale b b3 b4 b5 b6 r := by
  dsimp [saddleThirdCorrectionScale]
  have h0 : 0 ≤ saddleCorrectionScale b b3 b4 r := by
    dsimp [saddleCorrectionScale]
    positivity
  dsimp [saddleCorrectionScale] at h0
  have h2 : 0 ≤ |b3 r * b5 r| / (b r) ^ 4 := by positivity
  have h3 : 0 ≤ (b4 r) ^ 2 / (b r) ^ 4 := by positivity
  have h4 : 0 ≤ (b3 r) ^ 2 * |b4 r| / (b r) ^ 5 := by positivity
  have h5 : 0 ≤ (b3 r) ^ 4 / (b r) ^ 6 := by positivity
  nlinarith

private lemma saddleThirdScale_term_b3b5_le
    {b b3 b4 b5 b6 : ℝ → ℝ} {r : ℝ} (hb : 0 < b r) :
    |b3 r * b5 r| / (b r) ^ 4 ≤
      saddleThirdCorrectionScale b b3 b4 b5 b6 r := by
  dsimp [saddleThirdCorrectionScale]
  have h0 : 0 ≤ saddleCorrectionScale b b3 b4 r := by
    dsimp [saddleCorrectionScale]
    positivity
  dsimp [saddleCorrectionScale] at h0
  have h1 : 0 ≤ |b6 r| / (b r) ^ 3 := by positivity
  have h3 : 0 ≤ (b4 r) ^ 2 / (b r) ^ 4 := by positivity
  have h4 : 0 ≤ (b3 r) ^ 2 * |b4 r| / (b r) ^ 5 := by positivity
  have h5 : 0 ≤ (b3 r) ^ 4 / (b r) ^ 6 := by positivity
  nlinarith

private lemma saddleThirdScale_term_b4sq_le
    {b b3 b4 b5 b6 : ℝ → ℝ} {r : ℝ} (hb : 0 < b r) :
    (b4 r) ^ 2 / (b r) ^ 4 ≤ saddleThirdCorrectionScale b b3 b4 b5 b6 r := by
  dsimp [saddleThirdCorrectionScale]
  have h0 : 0 ≤ saddleCorrectionScale b b3 b4 r := by
    dsimp [saddleCorrectionScale]
    positivity
  dsimp [saddleCorrectionScale] at h0
  have h1 : 0 ≤ |b6 r| / (b r) ^ 3 := by positivity
  have h2 : 0 ≤ |b3 r * b5 r| / (b r) ^ 4 := by positivity
  have h4 : 0 ≤ (b3 r) ^ 2 * |b4 r| / (b r) ^ 5 := by positivity
  have h5 : 0 ≤ (b3 r) ^ 4 / (b r) ^ 6 := by positivity
  nlinarith

private lemma saddleThirdScale_term_b3sqb4_le
    {b b3 b4 b5 b6 : ℝ → ℝ} {r : ℝ} (hb : 0 < b r) :
    (b3 r) ^ 2 * |b4 r| / (b r) ^ 5 ≤
      saddleThirdCorrectionScale b b3 b4 b5 b6 r := by
  dsimp [saddleThirdCorrectionScale]
  have h0 : 0 ≤ saddleCorrectionScale b b3 b4 r := by
    dsimp [saddleCorrectionScale]
    positivity
  dsimp [saddleCorrectionScale] at h0
  have h1 : 0 ≤ |b6 r| / (b r) ^ 3 := by positivity
  have h2 : 0 ≤ |b3 r * b5 r| / (b r) ^ 4 := by positivity
  have h3 : 0 ≤ (b4 r) ^ 2 / (b r) ^ 4 := by positivity
  have h5 : 0 ≤ (b3 r) ^ 4 / (b r) ^ 6 := by positivity
  nlinarith

private lemma saddleThirdScale_term_b3four_le
    {b b3 b4 b5 b6 : ℝ → ℝ} {r : ℝ} (hb : 0 < b r) :
    (b3 r) ^ 4 / (b r) ^ 6 ≤ saddleThirdCorrectionScale b b3 b4 b5 b6 r := by
  dsimp [saddleThirdCorrectionScale]
  have h0 : 0 ≤ saddleCorrectionScale b b3 b4 r := by
    dsimp [saddleCorrectionScale]
    positivity
  dsimp [saddleCorrectionScale] at h0
  have h1 : 0 ≤ |b6 r| / (b r) ^ 3 := by positivity
  have h2 : 0 ≤ |b3 r * b5 r| / (b r) ^ 4 := by positivity
  have h3 : 0 ≤ (b4 r) ^ 2 / (b r) ^ 4 := by positivity
  have h4 : 0 ≤ (b3 r) ^ 2 * |b4 r| / (b r) ^ 5 := by positivity
  nlinarith

lemma saddleThirdPoly_quarticCoeff_norm_le_scale
    {b b3 b4 b5 b6 : ℝ → ℝ} {r : ℝ} (hb : 0 < b r) :
    ‖(b4 r : ℂ) / (24 * (b r : ℂ) ^ 2)‖ ≤
      (1 / 24 : ℝ) * saddleThirdCorrectionScale b b3 b4 b5 b6 r := by
  calc
    ‖(b4 r : ℂ) / (24 * (b r : ℂ) ^ 2)‖
        ≤ (1 / 24 : ℝ) * saddleCorrectionScale b b3 b4 r :=
          saddleSecondPoly_quarticCoeff_norm_le_scale (b := b) (b3 := b3)
            (b4 := b4) (r := r) hb
    _ ≤ (1 / 24 : ℝ) * saddleThirdCorrectionScale b b3 b4 b5 b6 r :=
          mul_le_mul_of_nonneg_left
            (saddleCorrectionScale_le_saddleThirdCorrectionScale
              (b := b) (b3 := b3) (b4 := b4) (b5 := b5) (b6 := b6) hb)
            (by norm_num)

lemma saddleThirdPoly_sexticB3Coeff_norm_le_scale
    {b b3 b4 b5 b6 : ℝ → ℝ} {r : ℝ} (hb : 0 < b r) :
    ‖(((b3 r) ^ 2 : ℝ) : ℂ) / (72 * (b r : ℂ) ^ 3)‖ ≤
      (1 / 72 : ℝ) * saddleThirdCorrectionScale b b3 b4 b5 b6 r := by
  calc
    ‖(((b3 r) ^ 2 : ℝ) : ℂ) / (72 * (b r : ℂ) ^ 3)‖
        ≤ (1 / 72 : ℝ) * saddleCorrectionScale b b3 b4 r :=
          saddleSecondPoly_sexticCoeff_norm_le_scale (b := b) (b3 := b3)
            (b4 := b4) (r := r) hb
    _ ≤ (1 / 72 : ℝ) * saddleThirdCorrectionScale b b3 b4 b5 b6 r :=
          mul_le_mul_of_nonneg_left
            (saddleCorrectionScale_le_saddleThirdCorrectionScale
              (b := b) (b3 := b3) (b4 := b4) (b5 := b5) (b6 := b6) hb)
            (by norm_num)

lemma saddleThirdPoly_b6Coeff_norm_le_scale
    {b b3 b4 b5 b6 : ℝ → ℝ} {r : ℝ} (hb : 0 < b r) :
    ‖(b6 r : ℂ) / (720 * (b r : ℂ) ^ 3)‖ ≤
      (1 / 720 : ℝ) * saddleThirdCorrectionScale b b3 b4 b5 b6 r := by
  calc
    ‖(b6 r : ℂ) / (720 * (b r : ℂ) ^ 3)‖
        = |b6 r| / (720 * (b r) ^ 3) := by
          simp [norm_pow, Real.norm_eq_abs, abs_of_pos hb]
    _ = (1 / 720 : ℝ) * (|b6 r| / (b r) ^ 3) := by ring
    _ ≤ (1 / 720 : ℝ) * saddleThirdCorrectionScale b b3 b4 b5 b6 r :=
          mul_le_mul_of_nonneg_left
            (saddleThirdScale_term_b6_le
              (b := b) (b3 := b3) (b4 := b4) (b5 := b5) (b6 := b6) hb)
            (by norm_num)

lemma saddleThirdPoly_b3b5Coeff_norm_le_scale
    {b b3 b4 b5 b6 : ℝ → ℝ} {r : ℝ} (hb : 0 < b r) :
    ‖(((b3 r * b5 r : ℝ) : ℂ) / (720 * (b r : ℂ) ^ 4))‖ ≤
      (1 / 720 : ℝ) * saddleThirdCorrectionScale b b3 b4 b5 b6 r := by
  calc
    ‖(((b3 r * b5 r : ℝ) : ℂ) / (720 * (b r : ℂ) ^ 4))‖
        = |b3 r * b5 r| / (720 * (b r) ^ 4) := by
          simp [norm_pow, Real.norm_eq_abs, abs_of_pos hb]
    _ = (1 / 720 : ℝ) * (|b3 r * b5 r| / (b r) ^ 4) := by ring
    _ ≤ (1 / 720 : ℝ) * saddleThirdCorrectionScale b b3 b4 b5 b6 r :=
          mul_le_mul_of_nonneg_left
            (saddleThirdScale_term_b3b5_le
              (b := b) (b3 := b3) (b4 := b4) (b5 := b5) (b6 := b6) hb)
            (by norm_num)

lemma saddleThirdPoly_b4sqCoeff_norm_le_scale
    {b b3 b4 b5 b6 : ℝ → ℝ} {r : ℝ} (hb : 0 < b r) :
    ‖((((b4 r) ^ 2 : ℝ) : ℂ) / (1152 * (b r : ℂ) ^ 4))‖ ≤
      (1 / 1152 : ℝ) * saddleThirdCorrectionScale b b3 b4 b5 b6 r := by
  calc
    ‖((((b4 r) ^ 2 : ℝ) : ℂ) / (1152 * (b r : ℂ) ^ 4))‖
        = (b4 r) ^ 2 / (1152 * (b r) ^ 4) := by
          simp [norm_pow, Real.norm_eq_abs, abs_of_pos hb]
    _ = (1 / 1152 : ℝ) * ((b4 r) ^ 2 / (b r) ^ 4) := by ring
    _ ≤ (1 / 1152 : ℝ) * saddleThirdCorrectionScale b b3 b4 b5 b6 r :=
          mul_le_mul_of_nonneg_left
            (saddleThirdScale_term_b4sq_le
              (b := b) (b3 := b3) (b4 := b4) (b5 := b5) (b6 := b6) hb)
            (by norm_num)

lemma saddleThirdPoly_b3sqb4Coeff_norm_le_scale
    {b b3 b4 b5 b6 : ℝ → ℝ} {r : ℝ} (hb : 0 < b r) :
    ‖((((b3 r) ^ 2 * b4 r : ℝ) : ℂ) / (1728 * (b r : ℂ) ^ 5))‖ ≤
      (1 / 1728 : ℝ) * saddleThirdCorrectionScale b b3 b4 b5 b6 r := by
  have hsq : 0 ≤ (b3 r) ^ 2 := sq_nonneg _
  calc
    ‖((((b3 r) ^ 2 * b4 r : ℝ) : ℂ) / (1728 * (b r : ℂ) ^ 5))‖
        = ((b3 r) ^ 2 * |b4 r|) / (1728 * (b r) ^ 5) := by
          simp [norm_pow, Real.norm_eq_abs, abs_of_pos hb, abs_mul, abs_of_nonneg hsq]
    _ = (1 / 1728 : ℝ) * (((b3 r) ^ 2 * |b4 r|) / (b r) ^ 5) := by ring
    _ ≤ (1 / 1728 : ℝ) * saddleThirdCorrectionScale b b3 b4 b5 b6 r :=
          mul_le_mul_of_nonneg_left
            (saddleThirdScale_term_b3sqb4_le
              (b := b) (b3 := b3) (b4 := b4) (b5 := b5) (b6 := b6) hb)
            (by norm_num)

lemma saddleThirdPoly_b3fourCoeff_norm_le_scale
    {b b3 b4 b5 b6 : ℝ → ℝ} {r : ℝ} (hb : 0 < b r) :
    ‖((((b3 r) ^ 4 : ℝ) : ℂ) / (31104 * (b r : ℂ) ^ 6))‖ ≤
      (1 / 31104 : ℝ) * saddleThirdCorrectionScale b b3 b4 b5 b6 r := by
  have hpow : 0 ≤ (b3 r) ^ 4 := by positivity
  have habs_pow : |b3 r| ^ 4 = (b3 r) ^ 4 := by
    rw [← abs_pow, abs_of_nonneg hpow]
  calc
    ‖((((b3 r) ^ 4 : ℝ) : ℂ) / (31104 * (b r : ℂ) ^ 6))‖
        = (b3 r) ^ 4 / (31104 * (b r) ^ 6) := by
          simp [norm_pow, Real.norm_eq_abs, abs_of_pos hb, abs_of_nonneg hpow,
            habs_pow]
    _ = (1 / 31104 : ℝ) * (((b3 r) ^ 4) / (b r) ^ 6) := by ring
    _ ≤ (1 / 31104 : ℝ) * saddleThirdCorrectionScale b b3 b4 b5 b6 r :=
          mul_le_mul_of_nonneg_left
            (saddleThirdScale_term_b3four_le
              (b := b) (b3 := b3) (b4 := b4) (b5 := b5) (b6 := b6) hb)
            (by norm_num)

private def gaussianMGFCoreThird (t : ℝ) : ℝ :=
  Real.exp (t ^ 2 / 2)

private lemma deriv_gaussianMGFCoreThird :
    deriv gaussianMGFCoreThird = fun t : ℝ => t * gaussianMGFCoreThird t := by
  ext t
  unfold gaussianMGFCoreThird
  rw [_root_.deriv_exp (by fun_prop)]
  simp only [deriv_div_const, differentiableAt_const, differentiableAt_fun_id, Nat.cast_ofNat,
    DifferentiableAt.fun_pow, deriv_fun_mul, deriv_const', zero_mul, deriv_fun_pow,
    Nat.add_one_sub_one, pow_one, deriv_id'', mul_one, zero_add]
  ring

private lemma deriv_t_mul_gaussianMGFCoreThird :
    deriv (fun t : ℝ => t * gaussianMGFCoreThird t) =
      fun t : ℝ => (1 + t ^ 2) * gaussianMGFCoreThird t := by
  ext t
  rw [deriv_fun_mul (by fun_prop) (by unfold gaussianMGFCoreThird; fun_prop)]
  rw [deriv_gaussianMGFCoreThird]
  simp
  ring_nf

private lemma deriv_poly2_mul_gaussianMGFCoreThird :
    deriv (fun t : ℝ => (1 + t ^ 2) * gaussianMGFCoreThird t) =
      fun t : ℝ => (3 * t + t ^ 3) * gaussianMGFCoreThird t := by
  ext t
  rw [deriv_fun_mul (by fun_prop) (by unfold gaussianMGFCoreThird; fun_prop)]
  rw [deriv_gaussianMGFCoreThird]
  simp only [differentiableAt_const, differentiableAt_fun_id, Nat.cast_ofNat,
    DifferentiableAt.fun_pow, DifferentiableAt.add, deriv_fun_add, deriv_const',
    deriv_fun_pow, Nat.add_one_sub_one, pow_one, deriv_id'', mul_one, zero_add]
  ring_nf

private lemma deriv_poly3_mul_gaussianMGFCoreThird :
    deriv (fun t : ℝ => (3 * t + t ^ 3) * gaussianMGFCoreThird t) =
      fun t : ℝ => (3 + 6 * t ^ 2 + t ^ 4) * gaussianMGFCoreThird t := by
  ext t
  rw [deriv_fun_mul (by fun_prop) (by unfold gaussianMGFCoreThird; fun_prop)]
  rw [deriv_gaussianMGFCoreThird]
  simp only [differentiableAt_const, differentiableAt_fun_id, Nat.cast_ofNat,
    DifferentiableAt.fun_pow, DifferentiableAt.const_mul, DifferentiableAt.add,
    deriv_fun_add, deriv_const_mul, deriv_fun_pow, Nat.add_one_sub_one, pow_one,
    deriv_id'', mul_one]
  have hpoly : deriv (fun t : ℝ => 3 * t + t ^ 3) t = 3 + 3 * t ^ 2 := by
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    have hlin : deriv (fun y : ℝ => 3 * y) t = 3 := by
      rw [deriv_const_mul_field (u := (3 : ℝ)) (v := fun y : ℝ => y) (x := t)]
      simp [deriv_id'']
    have hpow : deriv (fun y : ℝ => y ^ 3) t = 3 * t ^ 2 := by
      rw [deriv_fun_pow (by fun_prop)]
      rw [deriv_id'']
      ring
    simpa [hlin, hpow]
  rw [hpoly]
  ring_nf

private lemma deriv_poly4_mul_gaussianMGFCoreThird :
    deriv (fun t : ℝ => (3 + 6 * t ^ 2 + t ^ 4) * gaussianMGFCoreThird t) =
      fun t : ℝ => (15 * t + 10 * t ^ 3 + t ^ 5) * gaussianMGFCoreThird t := by
  ext t
  rw [deriv_fun_mul (by fun_prop) (by unfold gaussianMGFCoreThird; fun_prop)]
  rw [deriv_gaussianMGFCoreThird]
  simp only [differentiableAt_const, differentiableAt_fun_id, Nat.cast_ofNat,
    DifferentiableAt.fun_pow, DifferentiableAt.const_mul, DifferentiableAt.add,
    deriv_fun_add, deriv_const', deriv_const_mul, deriv_fun_pow, Nat.add_one_sub_one,
    pow_one, deriv_id'', mul_one, zero_add]
  have hpoly :
      deriv (fun t : ℝ => 3 + 6 * t ^ 2 + t ^ 4) t =
        12 * t + 4 * t ^ 3 := by
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    have hconst : deriv (fun _ : ℝ => (3 : ℝ)) t = 0 := by
      rw [deriv_const']
    have hquad : deriv (fun y : ℝ => 6 * y ^ 2) t = 12 * t := by
      rw [deriv_const_mul_field (u := (6 : ℝ)) (v := fun y : ℝ => y ^ 2) (x := t)]
      rw [deriv_fun_pow (by fun_prop)]
      rw [deriv_id'']
      ring
    have hquart : deriv (fun y : ℝ => y ^ 4) t = 4 * t ^ 3 := by
      rw [deriv_fun_pow (by fun_prop)]
      rw [deriv_id'']
      ring
    simpa [hconst, hquad, hquart]
  rw [hpoly]
  ring_nf

private lemma deriv_poly5_mul_gaussianMGFCoreThird :
    deriv (fun t : ℝ => (15 * t + 10 * t ^ 3 + t ^ 5) * gaussianMGFCoreThird t) =
      fun t : ℝ => (15 + 45 * t ^ 2 + 15 * t ^ 4 + t ^ 6) *
        gaussianMGFCoreThird t := by
  ext t
  rw [deriv_fun_mul (by fun_prop) (by unfold gaussianMGFCoreThird; fun_prop)]
  rw [deriv_gaussianMGFCoreThird]
  simp only [differentiableAt_const, differentiableAt_fun_id, Nat.cast_ofNat,
    DifferentiableAt.fun_pow, DifferentiableAt.const_mul, DifferentiableAt.add,
    deriv_fun_add, deriv_const_mul, deriv_fun_pow, Nat.add_one_sub_one, pow_one,
    deriv_id'', mul_one]
  have hpoly :
      deriv (fun t : ℝ => 15 * t + 10 * t ^ 3 + t ^ 5) t =
        15 + 30 * t ^ 2 + 5 * t ^ 4 := by
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    have hlin : deriv (fun y : ℝ => 15 * y) t = 15 := by
      rw [deriv_const_mul_field (u := (15 : ℝ)) (v := fun y : ℝ => y) (x := t)]
      simp [deriv_id'']
    have hcubic : deriv (fun y : ℝ => 10 * y ^ 3) t = 30 * t ^ 2 := by
      rw [deriv_const_mul_field (u := (10 : ℝ)) (v := fun y : ℝ => y ^ 3) (x := t)]
      rw [deriv_fun_pow (by fun_prop)]
      rw [deriv_id'']
      ring
    have hquint : deriv (fun y : ℝ => y ^ 5) t = 5 * t ^ 4 := by
      rw [deriv_fun_pow (by fun_prop)]
      rw [deriv_id'']
      ring
    simpa [hlin, hcubic, hquint]
  rw [hpoly]
  ring_nf

private lemma deriv_poly6_mul_gaussianMGFCoreThird :
    deriv (fun t : ℝ => (15 + 45 * t ^ 2 + 15 * t ^ 4 + t ^ 6) *
        gaussianMGFCoreThird t) =
      fun t : ℝ => (105 * t + 105 * t ^ 3 + 21 * t ^ 5 + t ^ 7) *
        gaussianMGFCoreThird t := by
  ext t
  rw [deriv_fun_mul (by fun_prop) (by unfold gaussianMGFCoreThird; fun_prop)]
  rw [deriv_gaussianMGFCoreThird]
  rw [show deriv (fun t : ℝ => 15 + 45 * t ^ 2 + 15 * t ^ 4 + t ^ 6) t =
      90 * t + 60 * t ^ 3 + 6 * t ^ 5 by
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    simp only [deriv_const', deriv_const_mul, deriv_fun_mul, deriv_fun_pow,
      differentiableAt_fun_id, differentiableAt_const, DifferentiableAt.fun_pow,
      DifferentiableAt.const_mul, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one,
      deriv_id'', mul_one, zero_mul, add_zero, zero_add]
    ring_nf]
  ring_nf

private lemma deriv_poly7_mul_gaussianMGFCoreThird :
    deriv (fun t : ℝ => (105 * t + 105 * t ^ 3 + 21 * t ^ 5 + t ^ 7) *
        gaussianMGFCoreThird t) =
      fun t : ℝ => (105 + 420 * t ^ 2 + 210 * t ^ 4 + 28 * t ^ 6 + t ^ 8) *
        gaussianMGFCoreThird t := by
  ext t
  rw [deriv_fun_mul (by fun_prop) (by unfold gaussianMGFCoreThird; fun_prop)]
  rw [deriv_gaussianMGFCoreThird]
  have hderiv :
      deriv (fun t : ℝ => 105 * t + 105 * t ^ 3 + 21 * t ^ 5 + t ^ 7) t =
        105 + 315 * t ^ 2 + 105 * t ^ 4 + 7 * t ^ 6 := by
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    have hlin : deriv (fun y : ℝ => 105 * y) t = 105 := by
      rw [deriv_const_mul_field (u := (105 : ℝ)) (v := fun y : ℝ => y) (x := t)]
      simp [deriv_id'']
    have hcubic : deriv (fun y : ℝ => 105 * y ^ 3) t = 315 * t ^ 2 := by
      rw [deriv_const_mul_field (u := (105 : ℝ)) (v := fun y : ℝ => y ^ 3) (x := t)]
      rw [deriv_fun_pow (by fun_prop)]
      rw [deriv_id'']
      ring
    have hquint : deriv (fun y : ℝ => 21 * y ^ 5) t = 105 * t ^ 4 := by
      rw [deriv_const_mul_field (u := (21 : ℝ)) (v := fun y : ℝ => y ^ 5) (x := t)]
      rw [deriv_fun_pow (by fun_prop)]
      rw [deriv_id'']
      ring
    have hsept : deriv (fun y : ℝ => y ^ 7) t = 7 * t ^ 6 := by
      rw [deriv_fun_pow (by fun_prop)]
      rw [deriv_id'']
      ring
    simpa [hlin, hcubic, hquint, hsept]
  rw [hderiv]
  ring_nf

private lemma deriv_poly8_mul_gaussianMGFCoreThird :
    deriv (fun t : ℝ =>
        (105 + 420 * t ^ 2 + 210 * t ^ 4 + 28 * t ^ 6 + t ^ 8) *
          gaussianMGFCoreThird t) =
      fun t : ℝ => (945 * t + 1260 * t ^ 3 + 378 * t ^ 5 + 36 * t ^ 7 + t ^ 9) *
        gaussianMGFCoreThird t := by
  ext t
  rw [deriv_fun_mul (by fun_prop) (by unfold gaussianMGFCoreThird; fun_prop)]
  rw [deriv_gaussianMGFCoreThird]
  rw [show deriv (fun t : ℝ =>
      105 + 420 * t ^ 2 + 210 * t ^ 4 + 28 * t ^ 6 + t ^ 8) t =
      840 * t + 840 * t ^ 3 + 168 * t ^ 5 + 8 * t ^ 7 by
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    simp only [deriv_const', deriv_const_mul, deriv_fun_mul, deriv_fun_pow,
      differentiableAt_fun_id, differentiableAt_const, DifferentiableAt.fun_pow,
      DifferentiableAt.const_mul, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one,
      deriv_id'', mul_one, zero_mul, add_zero, zero_add]
    ring_nf]
  ring_nf

private lemma deriv_poly9_mul_gaussianMGFCoreThird :
    deriv (fun t : ℝ =>
        (945 * t + 1260 * t ^ 3 + 378 * t ^ 5 + 36 * t ^ 7 + t ^ 9) *
          gaussianMGFCoreThird t) =
      fun t : ℝ =>
        (945 + 4725 * t ^ 2 + 3150 * t ^ 4 + 630 * t ^ 6 + 45 * t ^ 8 + t ^ 10) *
          gaussianMGFCoreThird t := by
  ext t
  rw [deriv_fun_mul (by fun_prop) (by unfold gaussianMGFCoreThird; fun_prop)]
  rw [deriv_gaussianMGFCoreThird]
  have hderiv :
      deriv (fun t : ℝ =>
        945 * t + 1260 * t ^ 3 + 378 * t ^ 5 + 36 * t ^ 7 + t ^ 9) t =
        945 + 3780 * t ^ 2 + 1890 * t ^ 4 + 252 * t ^ 6 + 9 * t ^ 8 := by
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    have hlin : deriv (fun y : ℝ => 945 * y) t = 945 := by
      rw [deriv_const_mul_field (u := (945 : ℝ)) (v := fun y : ℝ => y) (x := t)]
      simp [deriv_id'']
    have hcubic : deriv (fun y : ℝ => 1260 * y ^ 3) t = 3780 * t ^ 2 := by
      rw [deriv_const_mul_field (u := (1260 : ℝ)) (v := fun y : ℝ => y ^ 3) (x := t)]
      rw [deriv_fun_pow (by fun_prop)]
      rw [deriv_id'']
      ring
    have hquint : deriv (fun y : ℝ => 378 * y ^ 5) t = 1890 * t ^ 4 := by
      rw [deriv_const_mul_field (u := (378 : ℝ)) (v := fun y : ℝ => y ^ 5) (x := t)]
      rw [deriv_fun_pow (by fun_prop)]
      rw [deriv_id'']
      ring
    have hsept : deriv (fun y : ℝ => 36 * y ^ 7) t = 252 * t ^ 6 := by
      rw [deriv_const_mul_field (u := (36 : ℝ)) (v := fun y : ℝ => y ^ 7) (x := t)]
      rw [deriv_fun_pow (by fun_prop)]
      rw [deriv_id'']
      ring
    have hnine : deriv (fun y : ℝ => y ^ 9) t = 9 * t ^ 8 := by
      rw [deriv_fun_pow (by fun_prop)]
      rw [deriv_id'']
      ring
    simpa [hlin, hcubic, hquint, hsept, hnine]
  rw [hderiv]
  ring_nf

private lemma deriv_poly10_mul_gaussianMGFCoreThird :
    deriv (fun t : ℝ =>
        (945 + 4725 * t ^ 2 + 3150 * t ^ 4 + 630 * t ^ 6 + 45 * t ^ 8 + t ^ 10) *
          gaussianMGFCoreThird t) =
      fun t : ℝ =>
        (10395 * t + 17325 * t ^ 3 + 6930 * t ^ 5 + 990 * t ^ 7 + 55 * t ^ 9 +
            t ^ 11) *
          gaussianMGFCoreThird t := by
  ext t
  rw [deriv_fun_mul (by fun_prop) (by unfold gaussianMGFCoreThird; fun_prop)]
  rw [deriv_gaussianMGFCoreThird]
  rw [show deriv (fun t : ℝ =>
      945 + 4725 * t ^ 2 + 3150 * t ^ 4 + 630 * t ^ 6 + 45 * t ^ 8 + t ^ 10) t =
      9450 * t + 12600 * t ^ 3 + 3780 * t ^ 5 + 360 * t ^ 7 + 10 * t ^ 9 by
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    simp only [deriv_const', deriv_const_mul, deriv_fun_mul, deriv_fun_pow,
      differentiableAt_fun_id, differentiableAt_const, DifferentiableAt.fun_pow,
      DifferentiableAt.const_mul, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one,
      deriv_id'', mul_one, zero_mul, add_zero, zero_add]
    ring_nf]
  ring_nf

private lemma deriv_poly11_mul_gaussianMGFCoreThird :
    deriv (fun t : ℝ =>
        (10395 * t + 17325 * t ^ 3 + 6930 * t ^ 5 + 990 * t ^ 7 + 55 * t ^ 9 +
            t ^ 11) *
          gaussianMGFCoreThird t) =
      fun t : ℝ =>
        (10395 + 62370 * t ^ 2 + 51975 * t ^ 4 + 13860 * t ^ 6 +
            1485 * t ^ 8 + 66 * t ^ 10 + t ^ 12) *
          gaussianMGFCoreThird t := by
  ext t
  rw [deriv_fun_mul (by fun_prop) (by unfold gaussianMGFCoreThird; fun_prop)]
  rw [deriv_gaussianMGFCoreThird]
  have hderiv :
      deriv (fun t : ℝ =>
        10395 * t + 17325 * t ^ 3 + 6930 * t ^ 5 + 990 * t ^ 7 + 55 * t ^ 9 +
            t ^ 11) t =
        10395 + 51975 * t ^ 2 + 34650 * t ^ 4 + 6930 * t ^ 6 + 495 * t ^ 8 +
          11 * t ^ 10 := by
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    have hlin : deriv (fun y : ℝ => 10395 * y) t = 10395 := by
      rw [deriv_const_mul_field (u := (10395 : ℝ)) (v := fun y : ℝ => y) (x := t)]
      simp [deriv_id'']
    have hcubic : deriv (fun y : ℝ => 17325 * y ^ 3) t = 51975 * t ^ 2 := by
      rw [deriv_const_mul_field (u := (17325 : ℝ)) (v := fun y : ℝ => y ^ 3) (x := t)]
      rw [deriv_fun_pow (by fun_prop)]
      rw [deriv_id'']
      ring
    have hquint : deriv (fun y : ℝ => 6930 * y ^ 5) t = 34650 * t ^ 4 := by
      rw [deriv_const_mul_field (u := (6930 : ℝ)) (v := fun y : ℝ => y ^ 5) (x := t)]
      rw [deriv_fun_pow (by fun_prop)]
      rw [deriv_id'']
      ring
    have hsept : deriv (fun y : ℝ => 990 * y ^ 7) t = 6930 * t ^ 6 := by
      rw [deriv_const_mul_field (u := (990 : ℝ)) (v := fun y : ℝ => y ^ 7) (x := t)]
      rw [deriv_fun_pow (by fun_prop)]
      rw [deriv_id'']
      ring
    have hnine : deriv (fun y : ℝ => 55 * y ^ 9) t = 495 * t ^ 8 := by
      rw [deriv_const_mul_field (u := (55 : ℝ)) (v := fun y : ℝ => y ^ 9) (x := t)]
      rw [deriv_fun_pow (by fun_prop)]
      rw [deriv_id'']
      ring
    have heleven : deriv (fun y : ℝ => y ^ 11) t = 11 * t ^ 10 := by
      rw [deriv_fun_pow (by fun_prop)]
      rw [deriv_id'']
      ring
    simpa [hlin, hcubic, hquint, hsept, hnine, heleven]
  rw [hderiv]
  ring_nf

private lemma gaussianReal_moment_eight :
    (∫ x : ℝ, x ^ 8 ∂(gaussianReal 0 1)) = (105 : ℝ) := by
  calc
    (∫ x : ℝ, x ^ 8 ∂(gaussianReal 0 1))
        = iteratedDeriv 8 (mgf (fun x : ℝ => x) (gaussianReal 0 1)) 0 := by
          rw [iteratedDeriv_mgf_zero] <;> simp
    _ = 105 := by
      rw [mgf_fun_id_gaussianReal]
      simp only [zero_mul, zero_add, NNReal.coe_one, one_mul]
      change iteratedDeriv 8 gaussianMGFCoreThird 0 = 105
      rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ,
        iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ,
        iteratedDeriv_succ, iteratedDeriv_one]
      rw [deriv_gaussianMGFCoreThird, deriv_t_mul_gaussianMGFCoreThird,
        deriv_poly2_mul_gaussianMGFCoreThird, deriv_poly3_mul_gaussianMGFCoreThird,
        deriv_poly4_mul_gaussianMGFCoreThird, deriv_poly5_mul_gaussianMGFCoreThird,
        deriv_poly6_mul_gaussianMGFCoreThird, deriv_poly7_mul_gaussianMGFCoreThird]
      simp [gaussianMGFCoreThird]

private lemma gaussianReal_moment_ten :
    (∫ x : ℝ, x ^ 10 ∂(gaussianReal 0 1)) = (945 : ℝ) := by
  calc
    (∫ x : ℝ, x ^ 10 ∂(gaussianReal 0 1))
        = iteratedDeriv 10 (mgf (fun x : ℝ => x) (gaussianReal 0 1)) 0 := by
          rw [iteratedDeriv_mgf_zero] <;> simp
    _ = 945 := by
      rw [mgf_fun_id_gaussianReal]
      simp only [zero_mul, zero_add, NNReal.coe_one, one_mul]
      change iteratedDeriv 10 gaussianMGFCoreThird 0 = 945
      rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ,
        iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ,
        iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one]
      rw [deriv_gaussianMGFCoreThird, deriv_t_mul_gaussianMGFCoreThird,
        deriv_poly2_mul_gaussianMGFCoreThird, deriv_poly3_mul_gaussianMGFCoreThird,
        deriv_poly4_mul_gaussianMGFCoreThird, deriv_poly5_mul_gaussianMGFCoreThird,
        deriv_poly6_mul_gaussianMGFCoreThird, deriv_poly7_mul_gaussianMGFCoreThird,
        deriv_poly8_mul_gaussianMGFCoreThird, deriv_poly9_mul_gaussianMGFCoreThird]
      simp [gaussianMGFCoreThird]

private lemma gaussianReal_moment_twelve :
    (∫ x : ℝ, x ^ 12 ∂(gaussianReal 0 1)) = (10395 : ℝ) := by
  calc
    (∫ x : ℝ, x ^ 12 ∂(gaussianReal 0 1))
        = iteratedDeriv 12 (mgf (fun x : ℝ => x) (gaussianReal 0 1)) 0 := by
          rw [iteratedDeriv_mgf_zero] <;> simp
    _ = 10395 := by
      rw [mgf_fun_id_gaussianReal]
      simp only [zero_mul, zero_add, NNReal.coe_one, one_mul]
      change iteratedDeriv 12 gaussianMGFCoreThird 0 = 10395
      rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ,
        iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ,
        iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ,
        iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one]
      rw [deriv_gaussianMGFCoreThird, deriv_t_mul_gaussianMGFCoreThird,
        deriv_poly2_mul_gaussianMGFCoreThird, deriv_poly3_mul_gaussianMGFCoreThird,
        deriv_poly4_mul_gaussianMGFCoreThird, deriv_poly5_mul_gaussianMGFCoreThird,
        deriv_poly6_mul_gaussianMGFCoreThird, deriv_poly7_mul_gaussianMGFCoreThird,
        deriv_poly8_mul_gaussianMGFCoreThird, deriv_poly9_mul_gaussianMGFCoreThird,
        deriv_poly10_mul_gaussianMGFCoreThird, deriv_poly11_mul_gaussianMGFCoreThird]
      simp [gaussianMGFCoreThird]

private lemma gaussian_weighted_moment_from_probability_third (k : ℕ) (m : ℝ)
    (hm : (∫ x : ℝ, x ^ k ∂(gaussianReal 0 1)) = m) :
    (∫ x : ℝ, Real.exp (-(x ^ 2) / 2) * x ^ k) =
      Real.sqrt (2 * Real.pi) * m := by
  have hprob :=
    integral_gaussianReal_eq_integral_smul
      (μ := (0 : ℝ)) (v := (1 : ℝ≥0))
      (f := fun x : ℝ => x ^ k) (by norm_num : (1 : ℝ≥0) ≠ 0)
  rw [hm] at hprob
  rw [show (∫ x : ℝ, gaussianPDFReal 0 1 x • x ^ k) =
      (Real.sqrt (2 * Real.pi))⁻¹ *
        ∫ x : ℝ, Real.exp (-(x ^ 2) / 2) * x ^ k by
        simp_rw [gaussianPDFReal_zero_one, smul_eq_mul]
        rw [← integral_const_mul]
        apply integral_congr_ae
        refine ae_of_all _ ?_
        intro x
        ring] at hprob
  have hsqrt_pos : 0 < Real.sqrt (2 * Real.pi) := by positivity
  have hsqrt_ne : Real.sqrt (2 * Real.pi) ≠ 0 := hsqrt_pos.ne'
  calc
    (∫ x : ℝ, Real.exp (-(x ^ 2) / 2) * x ^ k)
        = Real.sqrt (2 * Real.pi) *
            ((Real.sqrt (2 * Real.pi))⁻¹ *
              ∫ x : ℝ, Real.exp (-(x ^ 2) / 2) * x ^ k) := by
          field_simp [hsqrt_ne]
    _ = Real.sqrt (2 * Real.pi) * m := by rw [← hprob]

lemma gaussian_weighted_moment_eight :
    (∫ x : ℝ, Real.exp (-(x ^ 2) / 2) * x ^ 8) =
      105 * Real.sqrt (2 * Real.pi) := by
  calc
    (∫ x : ℝ, Real.exp (-(x ^ 2) / 2) * x ^ 8)
        = Real.sqrt (2 * Real.pi) * 105 :=
          gaussian_weighted_moment_from_probability_third 8 105 gaussianReal_moment_eight
    _ = 105 * Real.sqrt (2 * Real.pi) := by ring

lemma gaussian_weighted_moment_ten :
    (∫ x : ℝ, Real.exp (-(x ^ 2) / 2) * x ^ 10) =
      945 * Real.sqrt (2 * Real.pi) := by
  calc
    (∫ x : ℝ, Real.exp (-(x ^ 2) / 2) * x ^ 10)
        = Real.sqrt (2 * Real.pi) * 945 :=
          gaussian_weighted_moment_from_probability_third 10 945 gaussianReal_moment_ten
    _ = 945 * Real.sqrt (2 * Real.pi) := by ring

lemma gaussian_weighted_moment_twelve :
    (∫ x : ℝ, Real.exp (-(x ^ 2) / 2) * x ^ 12) =
      10395 * Real.sqrt (2 * Real.pi) := by
  calc
    (∫ x : ℝ, Real.exp (-(x ^ 2) / 2) * x ^ 12)
        = Real.sqrt (2 * Real.pi) * 10395 :=
          gaussian_weighted_moment_from_probability_third 12 10395
          gaussianReal_moment_twelve
    _ = 10395 * Real.sqrt (2 * Real.pi) := by ring

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

private lemma gaussian_weighted_integrable_five :
    Integrable (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * x ^ 5) := by
  simpa [show (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * x ^ 5) =
      (fun x : ℝ => x ^ 5 * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) by
        funext x
        ring_nf] using
    (integrable_rpow_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (-1 : ℝ) < 5))

private lemma gaussian_weighted_integrable_six :
    Integrable (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * x ^ 6) := by
  simpa [show (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * x ^ 6) =
      (fun x : ℝ => x ^ 6 * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) by
        funext x
        ring_nf] using
    (integrable_rpow_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (-1 : ℝ) < 6))

private lemma gaussian_weighted_integrable_seven :
    Integrable (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * x ^ 7) := by
  simpa [show (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * x ^ 7) =
      (fun x : ℝ => x ^ 7 * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) by
        funext x
        ring_nf] using
    (integrable_rpow_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (-1 : ℝ) < 7))

private lemma gaussian_weighted_integrable_eight :
    Integrable (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * x ^ 8) := by
  simpa [show (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * x ^ 8) =
      (fun x : ℝ => x ^ 8 * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) by
        funext x
        ring_nf] using
    (integrable_rpow_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (-1 : ℝ) < 8))

private lemma gaussian_weighted_integrable_nine :
    Integrable (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * x ^ 9) := by
  simpa [show (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * x ^ 9) =
      (fun x : ℝ => x ^ 9 * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) by
        funext x
        ring_nf] using
    (integrable_rpow_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (-1 : ℝ) < 9))

private lemma gaussian_weighted_integrable_ten :
    Integrable (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * x ^ 10) := by
  simpa [show (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * x ^ 10) =
      (fun x : ℝ => x ^ 10 * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) by
        funext x
        ring_nf] using
    (integrable_rpow_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (-1 : ℝ) < 10))

private lemma gaussian_weighted_integrable_twelve :
    Integrable (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * x ^ 12) := by
  simpa [show (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * x ^ 12) =
      (fun x : ℝ => x ^ 12 * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) by
        funext x
        ring_nf] using
    (integrable_rpow_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (-1 : ℝ) < 12))

private lemma gaussian_complex_integrable_zero :
    Integrable (fun x : ℝ => Complex.exp (-(x ^ 2) / 2)) := by
  simpa using (gaussian_weighted_integrable_zero.ofReal (𝕜 := ℂ))

private lemma gaussian_complex_integrable_three :
    Integrable (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 3) := by
  simpa using (gaussian_weighted_integrable_three.ofReal (𝕜 := ℂ))

private lemma gaussian_complex_integrable_four :
    Integrable (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 4) := by
  simpa using (gaussian_weighted_integrable_four.ofReal (𝕜 := ℂ))

private lemma gaussian_complex_integrable_five :
    Integrable (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 5) := by
  simpa using (gaussian_weighted_integrable_five.ofReal (𝕜 := ℂ))

private lemma gaussian_complex_integrable_six :
    Integrable (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6) := by
  simpa using (gaussian_weighted_integrable_six.ofReal (𝕜 := ℂ))

private lemma gaussian_complex_integrable_seven :
    Integrable (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 7) := by
  simpa using (gaussian_weighted_integrable_seven.ofReal (𝕜 := ℂ))

private lemma gaussian_complex_integrable_eight :
    Integrable (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8) := by
  simpa using (gaussian_weighted_integrable_eight.ofReal (𝕜 := ℂ))

private lemma gaussian_complex_integrable_nine :
    Integrable (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 9) := by
  simpa using (gaussian_weighted_integrable_nine.ofReal (𝕜 := ℂ))

private lemma gaussian_complex_integrable_ten :
    Integrable (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 10) := by
  simpa using (gaussian_weighted_integrable_ten.ofReal (𝕜 := ℂ))

private lemma gaussian_complex_integrable_twelve :
    Integrable (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 12) := by
  simpa using (gaussian_weighted_integrable_twelve.ofReal (𝕜 := ℂ))

private lemma gaussian_complex_weighted_moment_odd_three :
    (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 3) = (0 : ℂ) := by
  rw [show (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 3) =
      (fun x : ℝ => ((Real.exp (-(x ^ 2) / 2) * x ^ 3 : ℝ) : ℂ)) by
        funext x
        simp]
  exact_mod_cast gaussian_weighted_moment_three

private lemma gaussian_complex_weighted_moment_odd_five :
    (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 5) = (0 : ℂ) := by
  let g : ℝ → ℂ := fun x => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 5
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

private lemma gaussian_complex_weighted_moment_odd_seven :
    (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 7) = (0 : ℂ) := by
  let g : ℝ → ℂ := fun x => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 7
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

private lemma gaussian_complex_weighted_moment_odd_nine :
    (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 9) = (0 : ℂ) := by
  let g : ℝ → ℂ := fun x => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 9
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

private lemma gaussian_complex_weighted_moment_eight :
    (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8) =
      (105 * Real.sqrt (2 * Real.pi) : ℂ) := by
  rw [show (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8) =
      (fun x : ℝ => ((Real.exp (-(x ^ 2) / 2) * x ^ 8 : ℝ) : ℂ)) by
        funext x
        simp]
  exact_mod_cast gaussian_weighted_moment_eight

private lemma gaussian_complex_weighted_moment_ten :
    (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 10) =
      (945 * Real.sqrt (2 * Real.pi) : ℂ) := by
  rw [show (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 10) =
      (fun x : ℝ => ((Real.exp (-(x ^ 2) / 2) * x ^ 10 : ℝ) : ℂ)) by
        funext x
        simp]
  exact_mod_cast gaussian_weighted_moment_ten

private lemma gaussian_complex_weighted_moment_twelve :
    (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 12) =
      (10395 * Real.sqrt (2 * Real.pi) : ℂ) := by
  rw [show (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 12) =
      (fun x : ℝ => ((Real.exp (-(x ^ 2) / 2) * x ^ 12 : ℝ) : ℂ)) by
        funext x
        simp]
  exact_mod_cast gaussian_weighted_moment_twelve

lemma gaussian_window_weighted_moment_five_eq_zero (L : ℝ) :
    (∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 5) = 0 := by
  let g : ℝ → ℂ := fun x => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 5
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

lemma gaussian_window_weighted_moment_seven_eq_zero (L : ℝ) :
    (∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 7) = 0 := by
  let g : ℝ → ℂ := fun x => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 7
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

lemma gaussian_window_weighted_moment_nine_eq_zero (L : ℝ) :
    (∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 9) = 0 := by
  let g : ℝ → ℂ := fun x => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 9
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

lemma gaussian_window_weighted_moment_eight_tendsto
    {L : ℕ → ℝ} (hL : Tendsto L atTop atTop) :
    Tendsto
      (fun n : ℕ =>
        ∫ x in -(L n)..(L n),
          Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8)
      atTop
      (𝓝 (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8)) :=
  intervalIntegral_tendsto_integral_symmetric gaussian_complex_integrable_eight hL

lemma gaussian_window_weighted_moment_ten_tendsto
    {L : ℕ → ℝ} (hL : Tendsto L atTop atTop) :
    Tendsto
      (fun n : ℕ =>
        ∫ x in -(L n)..(L n),
          Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 10)
      atTop
      (𝓝 (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 10)) :=
  intervalIntegral_tendsto_integral_symmetric gaussian_complex_integrable_ten hL

lemma gaussian_window_weighted_moment_twelve_tendsto
    {L : ℕ → ℝ} (hL : Tendsto L atTop atTop) :
    Tendsto
      (fun n : ℕ =>
        ∫ x in -(L n)..(L n),
          Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 12)
      atTop
      (𝓝 (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 12)) :=
  intervalIntegral_tendsto_integral_symmetric gaussian_complex_integrable_twelve hL

private lemma gaussian_complex_integrable_saddleSecondPoly_here
    (b b3 b4 : ℝ → ℝ) (r : ℝ) :
    Integrable (fun x : ℝ =>
      Complex.exp (-(x ^ 2) / 2) * saddleSecondPoly b b3 b4 r x) := by
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
  exact ((hF0.sub hF3).add hF4).sub hF6

/-- The third-order scalar correction is exactly the normalized even moments. -/
theorem saddleThirdCorrection_eq_gaussian_even_moments
    (b b3 b4 b5 b6 : ℝ → ℝ) (r : ℝ) :
    (saddleThirdCorrection b b3 b4 b5 b6 r : ℂ) =
      (1 / Real.sqrt (2 * Real.pi) : ℂ) *
        (-((b6 r : ℂ) / (720 * (b r : ℂ) ^ 3)) *
            (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6)
          + (((b3 r * b5 r : ℝ) : ℂ) / (720 * (b r : ℂ) ^ 4)) *
            (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8)
          + ((((b4 r) ^ 2 : ℝ) : ℂ) / (1152 * (b r : ℂ) ^ 4)) *
            (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8)
          - (((((b3 r) ^ 2 * b4 r : ℝ) : ℂ) / (1728 * (b r : ℂ) ^ 5)) *
            (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 10))
          + ((((b3 r) ^ 4 : ℝ) : ℂ) / (31104 * (b r : ℂ) ^ 6)) *
            (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 12)) := by
  rw [gaussian_complex_weighted_moment_six, gaussian_complex_weighted_moment_eight,
    gaussian_complex_weighted_moment_ten, gaussian_complex_weighted_moment_twelve]
  simp only [saddleThirdCorrection_apply, ofReal_add, ofReal_sub, ofReal_div, ofReal_neg,
    ofReal_mul, ofReal_ofNat, ofReal_pow, Nat.ofNat_nonneg, Real.sqrt_mul, one_div,
    mul_inv_rev, neg_mul]
  have hsqrt_ne : (Real.sqrt (2 * Real.pi) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (by positivity)
  field_simp [hsqrt_ne]
  ring_nf

/--
Integrating the universal third-order polynomial against the Gaussian produces
the first and second scalar saddle corrections.
-/
theorem gaussian_integral_saddleThirdPoly (b b3 b4 b5 b6 : ℝ → ℝ) (r : ℝ) :
    (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * saddleThirdPoly b b3 b4 b5 b6 r x) =
      (Real.sqrt (2 * Real.pi) : ℂ) *
        (1 + (saddleCorrection b b3 b4 r : ℂ) +
          (saddleThirdCorrection b b3 b4 b5 b6 r : ℂ)) := by
  let C5 : ℂ := Complex.I * ((b5 r : ℂ) /
    (120 * (Real.sqrt (b r) : ℂ) ^ 5))
  let C6 : ℂ := (b6 r : ℂ) / (720 * (b r : ℂ) ^ 3)
  let C7 : ℂ := Complex.I * (((b3 r * b4 r : ℝ) : ℂ) /
    (144 * (Real.sqrt (b r) : ℂ) ^ 3 * (b r : ℂ) ^ 2))
  let C8a : ℂ := ((b3 r * b5 r : ℝ) : ℂ) / (720 * (b r : ℂ) ^ 4)
  let C8b : ℂ := (((b4 r) ^ 2 : ℝ) : ℂ) / (1152 * (b r : ℂ) ^ 4)
  let C9 : ℂ := Complex.I * ((((b3 r) ^ 3 : ℝ) : ℂ) /
    (1296 * (Real.sqrt (b r) : ℂ) ^ 9))
  let C10 : ℂ := (((b3 r) ^ 2 * b4 r : ℝ) : ℂ) /
    (1728 * (b r : ℂ) ^ 5)
  let C12 : ℂ := (((b3 r) ^ 4 : ℝ) : ℂ) / (31104 * (b r : ℂ) ^ 6)
  let P2 : ℝ → ℂ := fun x =>
    Complex.exp (-(x ^ 2) / 2) * saddleSecondPoly b b3 b4 r x
  let F5 : ℝ → ℂ := fun x => C5 * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 5)
  let F6 : ℝ → ℂ := fun x => C6 * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6)
  let F7 : ℝ → ℂ := fun x => C7 * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 7)
  let F8a : ℝ → ℂ := fun x => C8a * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8)
  let F8b : ℝ → ℂ := fun x => C8b * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8)
  let F9 : ℝ → ℂ := fun x => C9 * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 9)
  let F10 : ℝ → ℂ := fun x => C10 * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 10)
  let F12 : ℝ → ℂ := fun x => C12 * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 12)
  have hpoly :
      (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) *
        saddleThirdPoly b b3 b4 b5 b6 r x) =
        fun x : ℝ => (P2 + F5 - F6 - F7 + F8a + F8b + F9 - F10 + F12) x := by
    funext x
    simp [P2, F5, F6, F7, F8a, F8b, F9, F10, F12, C5, C6, C7, C8a, C8b,
      C9, C10, C12, saddleThirdPoly]
    ring
  rw [hpoly]
  have hP2 : Integrable P2 := by
    simpa [P2] using gaussian_complex_integrable_saddleSecondPoly_here b b3 b4 r
  have hF5 : Integrable F5 := by
    simpa [F5] using gaussian_complex_integrable_five.const_mul C5
  have hF6 : Integrable F6 := by
    simpa [F6] using gaussian_complex_integrable_six.const_mul C6
  have hF7 : Integrable F7 := by
    simpa [F7] using gaussian_complex_integrable_seven.const_mul C7
  have hF8a : Integrable F8a := by
    simpa [F8a] using gaussian_complex_integrable_eight.const_mul C8a
  have hF8b : Integrable F8b := by
    simpa [F8b] using gaussian_complex_integrable_eight.const_mul C8b
  have hF9 : Integrable F9 := by
    simpa [F9] using gaussian_complex_integrable_nine.const_mul C9
  have hF10 : Integrable F10 := by
    simpa [F10] using gaussian_complex_integrable_ten.const_mul C10
  have hF12 : Integrable F12 := by
    simpa [F12] using gaussian_complex_integrable_twelve.const_mul C12
  have h25 : Integrable (fun x : ℝ => P2 x + F5 x) := hP2.add hF5
  have h256 : Integrable (fun x : ℝ => P2 x + F5 x - F6 x) := h25.sub hF6
  have h2567 : Integrable (fun x : ℝ => P2 x + F5 x - F6 x - F7 x) := h256.sub hF7
  have h25678a : Integrable (fun x : ℝ => P2 x + F5 x - F6 x - F7 x + F8a x) :=
    h2567.add hF8a
  have h25678ab :
      Integrable (fun x : ℝ => P2 x + F5 x - F6 x - F7 x + F8a x + F8b x) :=
    h25678a.add hF8b
  have h25678ab9 :
      Integrable (fun x : ℝ => P2 x + F5 x - F6 x - F7 x + F8a x + F8b x + F9 x) :=
    h25678ab.add hF9
  have h25678ab910 :
      Integrable (fun x : ℝ =>
        P2 x + F5 x - F6 x - F7 x + F8a x + F8b x + F9 x - F10 x) :=
    h25678ab9.sub hF10
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [integral_add h25678ab910 hF12]
  rw [integral_sub h25678ab9 hF10]
  rw [integral_add h25678ab hF9]
  rw [integral_add h25678a hF8b]
  rw [integral_add h2567 hF8a]
  rw [integral_sub h256 hF7]
  rw [integral_sub h25 hF6]
  rw [integral_add hP2 hF5]
  simp only [P2, F5, F6, F7, F8a, F8b, F9, F10, F12]
  rw [gaussian_integral_saddleSecondPoly]
  have h5eval :
      (∫ x : ℝ, C5 * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 5)) =
        C5 * ∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 5 :=
    integral_const_mul C5
      (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 5)
  have h6eval :
      (∫ x : ℝ, C6 * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6)) =
        C6 * ∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6 :=
    integral_const_mul C6
      (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6)
  have h7eval :
      (∫ x : ℝ, C7 * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 7)) =
        C7 * ∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 7 :=
    integral_const_mul C7
      (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 7)
  have h8aeval :
      (∫ x : ℝ, C8a * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8)) =
        C8a * ∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8 :=
    integral_const_mul C8a
      (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8)
  have h8beval :
      (∫ x : ℝ, C8b * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8)) =
        C8b * ∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8 :=
    integral_const_mul C8b
      (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8)
  have h9eval :
      (∫ x : ℝ, C9 * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 9)) =
        C9 * ∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 9 :=
    integral_const_mul C9
      (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 9)
  have h10eval :
      (∫ x : ℝ, C10 * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 10)) =
        C10 * ∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 10 :=
    integral_const_mul C10
      (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 10)
  have h12eval :
      (∫ x : ℝ, C12 * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 12)) =
        C12 * ∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 12 :=
    integral_const_mul C12
      (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 12)
  rw [h5eval, h6eval, h7eval, h8aeval, h8beval, h9eval, h10eval, h12eval]
  rw [gaussian_complex_weighted_moment_odd_five,
    gaussian_complex_weighted_moment_six, gaussian_complex_weighted_moment_odd_seven,
    gaussian_complex_weighted_moment_eight,
    gaussian_complex_weighted_moment_odd_nine, gaussian_complex_weighted_moment_ten,
    gaussian_complex_weighted_moment_twelve]
  have hsqrt_ne : (Real.sqrt (2 * Real.pi) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (by positivity)
  simp only [mul_zero, add_zero, sub_zero]
  have hcorrRaw := saddleThirdCorrection_eq_gaussian_even_moments b b3 b4 b5 b6 r
  rw [gaussian_complex_weighted_moment_six, gaussian_complex_weighted_moment_eight,
    gaussian_complex_weighted_moment_ten, gaussian_complex_weighted_moment_twelve] at hcorrRaw
  let G : ℂ := (Real.sqrt (2 * Real.pi) : ℂ)
  have hcorr :
      (saddleThirdCorrection b b3 b4 b5 b6 r : ℂ) =
        (1 / G) *
          (-C6 * (15 * G) + C8a * (105 * G) + C8b * (105 * G) -
            C10 * (945 * G) + C12 * (10395 * G)) := by
    simpa [G, C6, C8a, C8b, C10, C12] using hcorrRaw
  have hthird :
      -C6 * (15 * G) + C8a * (105 * G) + C8b * (105 * G) -
          C10 * (945 * G) + C12 * (10395 * G) =
        G * (saddleThirdCorrection b b3 b4 b5 b6 r : ℂ) := by
    calc
      -C6 * (15 * G) + C8a * (105 * G) + C8b * (105 * G) -
          C10 * (945 * G) + C12 * (10395 * G)
          = G * ((1 / G) *
              (-C6 * (15 * G) + C8a * (105 * G) + C8b * (105 * G) -
                C10 * (945 * G) + C12 * (10395 * G))) := by
              field_simp [G, hsqrt_ne]
      _ = G * (saddleThirdCorrection b b3 b4 b5 b6 r : ℂ) := by
            rw [← hcorr]
  rw [show (Real.sqrt (2 * Real.pi) : ℂ) = G by rfl]
  calc
    G * (1 + (saddleCorrection b b3 b4 r : ℂ)) - C6 * (15 * G) +
          C8a * (105 * G) + C8b * (105 * G) - C10 * (945 * G) +
          C12 * (10395 * G)
        = G * (1 + (saddleCorrection b b3 b4 r : ℂ)) +
            (-C6 * (15 * G) + C8a * (105 * G) + C8b * (105 * G) -
              C10 * (945 * G) + C12 * (10395 * G)) := by ring
    _ = G * (1 + (saddleCorrection b b3 b4 r : ℂ)) +
          G * (saddleThirdCorrection b b3 b4 b5 b6 r : ℂ) := by
          rw [hthird]
    _ = G * (1 + (saddleCorrection b b3 b4 r : ℂ) +
          (saddleThirdCorrection b b3 b4 b5 b6 r : ℂ)) := by ring

/--
Symmetric-window version of the third-order polynomial expansion.  The odd
terms of degrees `5`, `7`, and `9` vanish exactly on `[-L,L]`, as does the
cubic term already handled by the second-order window lemma.
-/
theorem gaussian_window_integral_saddleThirdPoly
    (b b3 b4 b5 b6 : ℝ → ℝ) (r L : ℝ) :
    (∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) *
        saddleThirdPoly b b3 b4 b5 b6 r x) =
      (∫ x in -L..L, Complex.exp (-(x ^ 2) / 2)) +
        ((b4 r : ℂ) / (24 * (b r : ℂ) ^ 2)) *
          (∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 4) -
        ((((b3 r) ^ 2 : ℝ) : ℂ) / (72 * (b r : ℂ) ^ 3)) *
          (∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6) -
        ((b6 r : ℂ) / (720 * (b r : ℂ) ^ 3)) *
          (∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6) +
        (((b3 r * b5 r : ℝ) : ℂ) / (720 * (b r : ℂ) ^ 4)) *
          (∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8) +
        ((((b4 r) ^ 2 : ℝ) : ℂ) / (1152 * (b r : ℂ) ^ 4)) *
          (∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8) -
        (((((b3 r) ^ 2 * b4 r : ℝ) : ℂ) / (1728 * (b r : ℂ) ^ 5)) *
          (∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 10)) +
        ((((b3 r) ^ 4 : ℝ) : ℂ) / (31104 * (b r : ℂ) ^ 6)) *
          (∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 12) := by
  let C5 : ℂ := Complex.I * ((b5 r : ℂ) /
    (120 * (Real.sqrt (b r) : ℂ) ^ 5))
  let C6 : ℂ := (b6 r : ℂ) / (720 * (b r : ℂ) ^ 3)
  let C7 : ℂ := Complex.I * (((b3 r * b4 r : ℝ) : ℂ) /
    (144 * (Real.sqrt (b r) : ℂ) ^ 3 * (b r : ℂ) ^ 2))
  let C8a : ℂ := ((b3 r * b5 r : ℝ) : ℂ) / (720 * (b r : ℂ) ^ 4)
  let C8b : ℂ := (((b4 r) ^ 2 : ℝ) : ℂ) / (1152 * (b r : ℂ) ^ 4)
  let C9 : ℂ := Complex.I * ((((b3 r) ^ 3 : ℝ) : ℂ) /
    (1296 * (Real.sqrt (b r) : ℂ) ^ 9))
  let C10 : ℂ := (((b3 r) ^ 2 * b4 r : ℝ) : ℂ) /
    (1728 * (b r : ℂ) ^ 5)
  let C12 : ℂ := (((b3 r) ^ 4 : ℝ) : ℂ) / (31104 * (b r : ℂ) ^ 6)
  let P2 : ℝ → ℂ := fun x =>
    Complex.exp (-(x ^ 2) / 2) * saddleSecondPoly b b3 b4 r x
  let F5 : ℝ → ℂ := fun x => C5 * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 5)
  let F6 : ℝ → ℂ := fun x => C6 * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6)
  let F7 : ℝ → ℂ := fun x => C7 * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 7)
  let F8a : ℝ → ℂ := fun x => C8a * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8)
  let F8b : ℝ → ℂ := fun x => C8b * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8)
  let F9 : ℝ → ℂ := fun x => C9 * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 9)
  let F10 : ℝ → ℂ := fun x => C10 * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 10)
  let F12 : ℝ → ℂ := fun x => C12 * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 12)
  have hpoly :
      (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) *
        saddleThirdPoly b b3 b4 b5 b6 r x) =
        fun x : ℝ => (P2 + F5 - F6 - F7 + F8a + F8b + F9 - F10 + F12) x := by
    funext x
    simp [P2, F5, F6, F7, F8a, F8b, F9, F10, F12, C5, C6, C7, C8a, C8b,
      C9, C10, C12, saddleThirdPoly]
    ring
  rw [hpoly]
  have hP2 : IntervalIntegrable P2 volume (-L) L := by
    have hcont : Continuous P2 := by
      unfold P2 saddleSecondPoly
      fun_prop
    exact hcont.intervalIntegrable _ _
  have hF5 : IntervalIntegrable F5 volume (-L) L := by
    have hcont : Continuous F5 := by
      unfold F5
      fun_prop
    exact hcont.intervalIntegrable _ _
  have hF6 : IntervalIntegrable F6 volume (-L) L := by
    have hcont : Continuous F6 := by
      unfold F6
      fun_prop
    exact hcont.intervalIntegrable _ _
  have hF7 : IntervalIntegrable F7 volume (-L) L := by
    have hcont : Continuous F7 := by
      unfold F7
      fun_prop
    exact hcont.intervalIntegrable _ _
  have hF8a : IntervalIntegrable F8a volume (-L) L := by
    have hcont : Continuous F8a := by
      unfold F8a
      fun_prop
    exact hcont.intervalIntegrable _ _
  have hF8b : IntervalIntegrable F8b volume (-L) L := by
    have hcont : Continuous F8b := by
      unfold F8b
      fun_prop
    exact hcont.intervalIntegrable _ _
  have hF9 : IntervalIntegrable F9 volume (-L) L := by
    have hcont : Continuous F9 := by
      unfold F9
      fun_prop
    exact hcont.intervalIntegrable _ _
  have hF10 : IntervalIntegrable F10 volume (-L) L := by
    have hcont : Continuous F10 := by
      unfold F10
      fun_prop
    exact hcont.intervalIntegrable _ _
  have hF12 : IntervalIntegrable F12 volume (-L) L := by
    have hcont : Continuous F12 := by
      unfold F12
      fun_prop
    exact hcont.intervalIntegrable _ _
  have h25 : IntervalIntegrable (fun x : ℝ => P2 x + F5 x) volume (-L) L :=
    hP2.add hF5
  have h256 : IntervalIntegrable (fun x : ℝ => P2 x + F5 x - F6 x) volume (-L) L :=
    h25.sub hF6
  have h2567 :
      IntervalIntegrable (fun x : ℝ => P2 x + F5 x - F6 x - F7 x) volume (-L) L :=
    h256.sub hF7
  have h25678a :
      IntervalIntegrable (fun x : ℝ => P2 x + F5 x - F6 x - F7 x + F8a x)
        volume (-L) L := h2567.add hF8a
  have h25678ab :
      IntervalIntegrable (fun x : ℝ => P2 x + F5 x - F6 x - F7 x + F8a x + F8b x)
        volume (-L) L := h25678a.add hF8b
  have h25678ab9 :
      IntervalIntegrable
        (fun x : ℝ => P2 x + F5 x - F6 x - F7 x + F8a x + F8b x + F9 x)
        volume (-L) L := h25678ab.add hF9
  have h25678ab910 :
      IntervalIntegrable
        (fun x : ℝ => P2 x + F5 x - F6 x - F7 x + F8a x + F8b x + F9 x - F10 x)
        volume (-L) L := h25678ab9.sub hF10
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [intervalIntegral.integral_add h25678ab910 hF12]
  rw [intervalIntegral.integral_sub h25678ab9 hF10]
  rw [intervalIntegral.integral_add h25678ab hF9]
  rw [intervalIntegral.integral_add h25678a hF8b]
  rw [intervalIntegral.integral_add h2567 hF8a]
  rw [intervalIntegral.integral_sub h256 hF7]
  rw [intervalIntegral.integral_sub h25 hF6]
  rw [intervalIntegral.integral_add hP2 hF5]
  simp only [P2, F5, F6, F7, F8a, F8b, F9, F10, F12]
  rw [gaussian_window_integral_saddleSecondPoly]
  have h5eval :
      (∫ x in -L..L, C5 * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 5)) =
        C5 * ∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 5 := by
    exact intervalIntegral.integral_const_mul C5
      (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 5)
  have h6eval :
      (∫ x in -L..L, C6 * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6)) =
        C6 * ∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6 := by
    exact intervalIntegral.integral_const_mul C6
      (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6)
  have h7eval :
      (∫ x in -L..L, C7 * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 7)) =
        C7 * ∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 7 := by
    exact intervalIntegral.integral_const_mul C7
      (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 7)
  have h8aeval :
      (∫ x in -L..L, C8a * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8)) =
        C8a * ∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8 := by
    exact intervalIntegral.integral_const_mul C8a
      (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8)
  have h8beval :
      (∫ x in -L..L, C8b * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8)) =
        C8b * ∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8 := by
    exact intervalIntegral.integral_const_mul C8b
      (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8)
  have h9eval :
      (∫ x in -L..L, C9 * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 9)) =
        C9 * ∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 9 := by
    exact intervalIntegral.integral_const_mul C9
      (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 9)
  have h10eval :
      (∫ x in -L..L, C10 * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 10)) =
        C10 * ∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 10 := by
    exact intervalIntegral.integral_const_mul C10
      (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 10)
  have h12eval :
      (∫ x in -L..L, C12 * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 12)) =
        C12 * ∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 12 := by
    exact intervalIntegral.integral_const_mul C12
      (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 12)
  rw [h5eval, h6eval, h7eval, h8aeval, h8beval, h9eval, h10eval, h12eval]
  rw [gaussian_window_weighted_moment_five_eq_zero,
    gaussian_window_weighted_moment_seven_eq_zero,
    gaussian_window_weighted_moment_nine_eq_zero]
  simp [C5, C6, C7, C8a, C8b, C9, C10, C12]
