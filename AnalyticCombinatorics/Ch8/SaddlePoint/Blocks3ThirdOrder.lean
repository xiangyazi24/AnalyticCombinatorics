import AnalyticCombinatorics.Ch8.SaddlePoint.ThirdOrderHAdmissible
import AnalyticCombinatorics.Ch8.SaddlePoint.Blocks3SecondOrder

/-!
# Third-order saddle data for blocks of size at most three

This file instantiates the third-order Hayman wrapper for
`exp (z + z^2 / 2 + z^3 / 6)`.  The fifth and sixth logarithmic saddle
derivatives are
`b_5(r)=r+16r^2+81r^3/2` and `b_6(r)=r+32r^2+243r^3/2`.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval PowerSeries

set_option maxHeartbeats 1400000
set_option linter.unusedSimpArgs false

noncomputable section

namespace Blocks3HAdmissible

/-- Fifth logarithmic saddle derivative for blocks of size at most three. -/
def blocks3SaddleB5Real (r : ℝ) : ℝ :=
  r + 16 * r ^ 2 + 81 * r ^ 3 / 2

/-- Sixth logarithmic saddle derivative for blocks of size at most three. -/
def blocks3SaddleB6Real (r : ℝ) : ℝ :=
  r + 32 * r ^ 2 + 243 * r ^ 3 / 2

/--
Third-order scale required by the current abstract interface.  The interface's
`saddleThirdCorrectionScale` includes the second-order absolute coefficient
scale, so this reusable scale is the existing second-order one.
-/
def blocks3ThirdCorrScale (r : ℝ) : ℝ :=
  blocks3SecondCorrScale r

/-- The explicit third-order correction at the saddle radius. -/
def blocks3ThirdCorrectionAtSaddle (n : ℕ) : ℝ :=
  saddleThirdCorrection blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real
    blocks3SaddleB5Real blocks3SaddleB6Real (blocks3SaddleRadius n)

/-- Error term for the formal blocks-<=3 EGF coefficient at third order. -/
def blocks3ThirdOrderSeriesError (n : ℕ) : ℂ :=
  blocks3Series.coeff n / blocks3SecondOrderSaddleScale n -
    (1 + (blocks3SecondCorrectionAtSaddle n : ℂ) +
      (blocks3ThirdCorrectionAtSaddle n : ℂ))

/-- Error term for `B_3(n) / n!` at third order. -/
def blocks3ThirdOrderNumberError (n : ℕ) : ℂ :=
  (((AnalyticCombinatorics.Ch1.CombClass.blocks3.counts n : ℝ) /
      n.factorial : ℝ) : ℂ) /
    blocks3SecondOrderSaddleScale n -
      (1 + (blocks3SecondCorrectionAtSaddle n : ℂ) +
        (blocks3ThirdCorrectionAtSaddle n : ℂ))

private lemma blocks3SaddleBReal_pos_of_ge_one {r : ℝ} (hr : 1 ≤ r) :
    0 < blocks3SaddleBReal r := by
  unfold blocks3SaddleBReal
  positivity

private lemma blocks3_b_ge_r_sq {r : ℝ} (hr : 1 ≤ r) :
    r ^ 2 ≤ blocks3SaddleBReal r := by
  unfold blocks3SaddleBReal
  nlinarith [hr, sq_nonneg r, show 0 ≤ r ^ 3 by positivity]

private lemma blocks3_b_ge_r_cubed {r : ℝ} (hr : 1 ≤ r) :
    r ^ 3 ≤ blocks3SaddleBReal r := by
  unfold blocks3SaddleBReal
  nlinarith [hr, sq_nonneg r, show 0 ≤ r ^ 2 by positivity,
    show 0 ≤ r ^ 3 by positivity]

private lemma blocks3_sqrtB_sq {r : ℝ} (hb : 0 < blocks3SaddleBReal r) :
    (Real.sqrt (blocks3SaddleBReal r)) ^ 2 = blocks3SaddleBReal r :=
  Real.sq_sqrt hb.le

private lemma blocks3_sqrtB_ge_r {r : ℝ} (hr : 1 ≤ r) :
    r ≤ Real.sqrt (blocks3SaddleBReal r) := by
  exact Real.le_sqrt_of_sq_le (blocks3_b_ge_r_sq hr)

private lemma blocks3_b_norm_eq_of_ge_one {r : ℝ} (hr : 1 ≤ r) :
    ‖(blocks3SaddleBReal r : ℂ)‖ = blocks3SaddleBReal r := by
  have hbpos : 0 < blocks3SaddleBReal r := blocks3SaddleBReal_pos_of_ge_one hr
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hbpos]

private lemma blocks3_sqrtB_norm_eq_of_ge_one {r : ℝ} (hr : 1 ≤ r) :
    ‖(Real.sqrt (blocks3SaddleBReal r) : ℂ)‖ =
      Real.sqrt (blocks3SaddleBReal r) := by
  have hbpos : 0 < blocks3SaddleBReal r := blocks3SaddleBReal_pos_of_ge_one hr
  have hsqrt_pos : 0 < Real.sqrt (blocks3SaddleBReal r) := Real.sqrt_pos.mpr hbpos
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsqrt_pos]

private lemma blocks3_one_le_r_sq {r : ℝ} (hr : 1 ≤ r) : 1 ≤ r ^ 2 := by
  nlinarith [sq_nonneg (r - 1)]

private lemma blocks3_r_sq_le_r_cubed {r : ℝ} (hr : 1 ≤ r) : r ^ 2 ≤ r ^ 3 := by
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  calc
    r ^ 2 = r ^ 2 * 1 := by ring
    _ ≤ r ^ 2 * r := mul_le_mul_of_nonneg_left hr (sq_nonneg r)
    _ = r ^ 3 := by ring

private lemma blocks3_r_le_r_cubed {r : ℝ} (hr : 1 ≤ r) : r ≤ r ^ 3 := by
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  calc
    r = r * 1 := by ring
    _ ≤ r * r ^ 2 := mul_le_mul_of_nonneg_left (blocks3_one_le_r_sq hr) hr0
    _ = r ^ 3 := by ring

private lemma blocks3_b3_nonneg_of_ge_one {r : ℝ} (hr : 1 ≤ r) :
    0 ≤ blocks3SaddleB3Real r := by
  unfold blocks3SaddleB3Real
  positivity

private lemma blocks3_b4_nonneg_of_ge_one {r : ℝ} (hr : 1 ≤ r) :
    0 ≤ blocks3SaddleB4Real r := by
  unfold blocks3SaddleB4Real
  positivity

private lemma blocks3_b5_nonneg_of_ge_one {r : ℝ} (hr : 1 ≤ r) :
    0 ≤ blocks3SaddleB5Real r := by
  unfold blocks3SaddleB5Real
  positivity

private lemma blocks3_b6_nonneg_of_ge_one {r : ℝ} (hr : 1 ≤ r) :
    0 ≤ blocks3SaddleB6Real r := by
  unfold blocks3SaddleB6Real
  positivity

private lemma blocks3_b3_le {r : ℝ} (hr : 1 ≤ r) :
    blocks3SaddleB3Real r ≤ 10 * r ^ 3 := by
  unfold blocks3SaddleB3Real
  nlinarith [blocks3_r_le_r_cubed hr, blocks3_r_sq_le_r_cubed hr]

private lemma blocks3_b4_le {r : ℝ} (hr : 1 ≤ r) :
    blocks3SaddleB4Real r ≤ 25 * r ^ 3 := by
  unfold blocks3SaddleB4Real
  nlinarith [blocks3_r_le_r_cubed hr, blocks3_r_sq_le_r_cubed hr]

private lemma blocks3_b5_le {r : ℝ} (hr : 1 ≤ r) :
    blocks3SaddleB5Real r ≤ 60 * r ^ 3 := by
  unfold blocks3SaddleB5Real
  nlinarith [blocks3_r_le_r_cubed hr, blocks3_r_sq_le_r_cubed hr]

private lemma blocks3_b6_le {r : ℝ} (hr : 1 ≤ r) :
    blocks3SaddleB6Real r ≤ 160 * r ^ 3 := by
  unfold blocks3SaddleB6Real
  nlinarith [blocks3_r_le_r_cubed hr, blocks3_r_sq_le_r_cubed hr]

private lemma blocks3_b_pow_three_ge_r_pow_nine {r : ℝ} (hr : 1 ≤ r) :
    r ^ 9 ≤ (blocks3SaddleBReal r) ^ 3 := by
  have hb_ge := blocks3_b_ge_r_cubed hr
  calc
    r ^ 9 = (r ^ 3) ^ 3 := by ring
    _ ≤ (blocks3SaddleBReal r) ^ 3 :=
      pow_le_pow_left₀ (by positivity) hb_ge 3

private lemma blocks3_b_pow_four_ge_r_pow_twelve {r : ℝ} (hr : 1 ≤ r) :
    r ^ 12 ≤ (blocks3SaddleBReal r) ^ 4 := by
  have hb_ge := blocks3_b_ge_r_cubed hr
  calc
    r ^ 12 = (r ^ 3) ^ 4 := by ring
    _ ≤ (blocks3SaddleBReal r) ^ 4 :=
      pow_le_pow_left₀ (by positivity) hb_ge 4

private lemma blocks3_b_pow_five_ge_r_pow_fifteen {r : ℝ} (hr : 1 ≤ r) :
    r ^ 15 ≤ (blocks3SaddleBReal r) ^ 5 := by
  have hb_ge := blocks3_b_ge_r_cubed hr
  calc
    r ^ 15 = (r ^ 3) ^ 5 := by ring
    _ ≤ (blocks3SaddleBReal r) ^ 5 :=
      pow_le_pow_left₀ (by positivity) hb_ge 5

private lemma blocks3_b_pow_six_ge_r_pow_eighteen {r : ℝ} (hr : 1 ≤ r) :
    r ^ 18 ≤ (blocks3SaddleBReal r) ^ 6 := by
  have hb_ge := blocks3_b_ge_r_cubed hr
  calc
    r ^ 18 = (r ^ 3) ^ 6 := by ring
    _ ≤ (blocks3SaddleBReal r) ^ 6 :=
      pow_le_pow_left₀ (by positivity) hb_ge 6

private lemma blocks3_sqrtB_pow_five_ge_r_pow_seven {r : ℝ} (hr : 1 ≤ r) :
    r ^ 7 ≤ (Real.sqrt (blocks3SaddleBReal r)) ^ 5 := by
  have hbpos : 0 < blocks3SaddleBReal r := blocks3SaddleBReal_pos_of_ge_one hr
  have hb2_ge : r ^ 6 ≤ (blocks3SaddleBReal r) ^ 2 := by
    have hb_ge := blocks3_b_ge_r_cubed hr
    calc
      r ^ 6 = (r ^ 3) ^ 2 := by ring
      _ ≤ (blocks3SaddleBReal r) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hb_ge 2
  have hsqrt_ge := blocks3_sqrtB_ge_r hr
  calc
    r ^ 7 = r ^ 6 * r := by ring
    _ ≤ (blocks3SaddleBReal r) ^ 2 * Real.sqrt (blocks3SaddleBReal r) :=
      mul_le_mul hb2_ge hsqrt_ge (by positivity) (by positivity)
    _ = (Real.sqrt (blocks3SaddleBReal r)) ^ 5 := by
      let s : ℝ := Real.sqrt (blocks3SaddleBReal r)
      change (blocks3SaddleBReal r) ^ 2 * s = s ^ 5
      have hs : s ^ 2 = blocks3SaddleBReal r := by
        dsimp [s]
        exact blocks3_sqrtB_sq hbpos
      rw [← hs]
      ring

private lemma blocks3_sqrtB_pow_three_mul_b_pow_two_ge_r_pow_ten {r : ℝ}
    (hr : 1 ≤ r) :
    r ^ 10 ≤ (Real.sqrt (blocks3SaddleBReal r)) ^ 3 *
      (blocks3SaddleBReal r) ^ 2 := by
  have hbpos : 0 < blocks3SaddleBReal r := blocks3SaddleBReal_pos_of_ge_one hr
  have hb3_ge := blocks3_b_pow_three_ge_r_pow_nine hr
  have hsqrt_ge := blocks3_sqrtB_ge_r hr
  calc
    r ^ 10 = r * r ^ 9 := by ring
    _ ≤ Real.sqrt (blocks3SaddleBReal r) * (blocks3SaddleBReal r) ^ 3 :=
      mul_le_mul hsqrt_ge hb3_ge (by positivity) (by positivity)
    _ = (Real.sqrt (blocks3SaddleBReal r)) ^ 3 *
        (blocks3SaddleBReal r) ^ 2 := by
      let s : ℝ := Real.sqrt (blocks3SaddleBReal r)
      change s * (blocks3SaddleBReal r) ^ 3 = s ^ 3 * (blocks3SaddleBReal r) ^ 2
      have hs : s ^ 2 = blocks3SaddleBReal r := by
        dsimp [s]
        exact blocks3_sqrtB_sq hbpos
      rw [← hs]
      ring

private lemma blocks3_sqrtB_pow_nine_ge_r_pow_thirteen {r : ℝ} (hr : 1 ≤ r) :
    r ^ 13 ≤ (Real.sqrt (blocks3SaddleBReal r)) ^ 9 := by
  have hbpos : 0 < blocks3SaddleBReal r := blocks3SaddleBReal_pos_of_ge_one hr
  have hb4_ge := blocks3_b_pow_four_ge_r_pow_twelve hr
  have hsqrt_ge := blocks3_sqrtB_ge_r hr
  calc
    r ^ 13 = r * r ^ 12 := by ring
    _ ≤ Real.sqrt (blocks3SaddleBReal r) * (blocks3SaddleBReal r) ^ 4 :=
      mul_le_mul hsqrt_ge hb4_ge (by positivity) (by positivity)
    _ = (Real.sqrt (blocks3SaddleBReal r)) ^ 9 := by
      let s : ℝ := Real.sqrt (blocks3SaddleBReal r)
      change s * (blocks3SaddleBReal r) ^ 4 = s ^ 9
      have hs : s ^ 2 = blocks3SaddleBReal r := by
        dsimp [s]
        exact blocks3_sqrtB_sq hbpos
      rw [← hs]
      ring

private lemma blocks3_rpow_neg_three_eq_inv_cube {r : ℝ} (hr : 0 < r) :
    r ^ (-(3 : ℝ)) = (r ^ 3)⁻¹ := by
  simpa using Real.rpow_neg hr.le (3 : ℝ)

private lemma blocks3_term_b6_le_thirdCorrScale {r : ℝ} (hr : 1 ≤ r) :
    |blocks3SaddleB6Real r| / (blocks3SaddleBReal r) ^ 3 ≤
      100000 * blocks3ThirdCorrScale r := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hb3_ge := blocks3_b_pow_three_ge_r_pow_nine hr
  have h1_le_r3 : 1 ≤ r ^ 3 := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ r * r ^ 2 :=
        mul_le_mul hr (blocks3_one_le_r_sq hr) zero_le_one (le_trans zero_le_one hr)
      _ = r ^ 3 := by ring
  unfold blocks3ThirdCorrScale blocks3SecondCorrScale
  rw [blocks3_rpow_neg_three_eq_inv_cube hrpos]
  rw [abs_of_nonneg (blocks3_b6_nonneg_of_ge_one hr)]
  calc
    blocks3SaddleB6Real r / (blocks3SaddleBReal r) ^ 3
        ≤ (160 * r ^ 3) / r ^ 9 := by
          exact div_le_div₀ (by positivity) (blocks3_b6_le hr) (by positivity)
            (by nlinarith [hb3_ge])
    _ ≤ 100000 * (r ^ 3)⁻¹ := by
      field_simp [hrpos.ne']
      nlinarith [h1_le_r3, show 0 ≤ r ^ 6 by positivity]

private lemma blocks3_term_b3b5_le_thirdCorrScale {r : ℝ} (hr : 1 ≤ r) :
    |blocks3SaddleB3Real r * blocks3SaddleB5Real r| /
        (blocks3SaddleBReal r) ^ 4 ≤
      100000 * blocks3ThirdCorrScale r := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hb4_ge := blocks3_b_pow_four_ge_r_pow_twelve hr
  have h1_le_r3 : 1 ≤ r ^ 3 := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ r * r ^ 2 :=
        mul_le_mul hr (blocks3_one_le_r_sq hr) zero_le_one (le_trans zero_le_one hr)
      _ = r ^ 3 := by ring
  have hnum_nonneg : 0 ≤ blocks3SaddleB3Real r * blocks3SaddleB5Real r :=
    mul_nonneg (blocks3_b3_nonneg_of_ge_one hr) (blocks3_b5_nonneg_of_ge_one hr)
  have hnum_le : blocks3SaddleB3Real r * blocks3SaddleB5Real r ≤ 600 * r ^ 6 := by
    calc
      blocks3SaddleB3Real r * blocks3SaddleB5Real r
          ≤ (10 * r ^ 3) * (60 * r ^ 3) :=
            mul_le_mul (blocks3_b3_le hr) (blocks3_b5_le hr)
              (blocks3_b5_nonneg_of_ge_one hr) (by positivity)
      _ = 600 * r ^ 6 := by ring
  unfold blocks3ThirdCorrScale blocks3SecondCorrScale
  rw [blocks3_rpow_neg_three_eq_inv_cube hrpos]
  rw [abs_of_nonneg hnum_nonneg]
  calc
    blocks3SaddleB3Real r * blocks3SaddleB5Real r /
        (blocks3SaddleBReal r) ^ 4
        ≤ (600 * r ^ 6) / r ^ 12 := by
          exact div_le_div₀ (by positivity) hnum_le (by positivity)
            (by nlinarith [hb4_ge])
    _ ≤ 100000 * (r ^ 3)⁻¹ := by
      field_simp [hrpos.ne']
      nlinarith [h1_le_r3, show 0 ≤ r ^ 9 by positivity]

private lemma blocks3_term_b4sq_le_thirdCorrScale {r : ℝ} (hr : 1 ≤ r) :
    (blocks3SaddleB4Real r) ^ 2 / (blocks3SaddleBReal r) ^ 4 ≤
      100000 * blocks3ThirdCorrScale r := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hb4_ge := blocks3_b_pow_four_ge_r_pow_twelve hr
  have h1_le_r3 : 1 ≤ r ^ 3 := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ r * r ^ 2 :=
        mul_le_mul hr (blocks3_one_le_r_sq hr) zero_le_one (le_trans zero_le_one hr)
      _ = r ^ 3 := by ring
  have hnum_le : (blocks3SaddleB4Real r) ^ 2 ≤ 625 * r ^ 6 := by
    calc
      (blocks3SaddleB4Real r) ^ 2 ≤ (25 * r ^ 3) ^ 2 :=
        pow_le_pow_left₀ (blocks3_b4_nonneg_of_ge_one hr) (blocks3_b4_le hr) 2
      _ = 625 * r ^ 6 := by ring
  unfold blocks3ThirdCorrScale blocks3SecondCorrScale
  rw [blocks3_rpow_neg_three_eq_inv_cube hrpos]
  calc
    (blocks3SaddleB4Real r) ^ 2 / (blocks3SaddleBReal r) ^ 4
        ≤ (625 * r ^ 6) / r ^ 12 := by
          exact div_le_div₀ (by positivity) hnum_le (by positivity)
            (by nlinarith [hb4_ge])
    _ ≤ 100000 * (r ^ 3)⁻¹ := by
      field_simp [hrpos.ne']
      nlinarith [h1_le_r3, show 0 ≤ r ^ 9 by positivity]

private lemma blocks3_term_b3sqb4_le_thirdCorrScale {r : ℝ} (hr : 1 ≤ r) :
    (blocks3SaddleB3Real r) ^ 2 * |blocks3SaddleB4Real r| /
        (blocks3SaddleBReal r) ^ 5 ≤
      100000 * blocks3ThirdCorrScale r := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hb5_ge := blocks3_b_pow_five_ge_r_pow_fifteen hr
  have h1_le_r3 : 1 ≤ r ^ 3 := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ r * r ^ 2 :=
        mul_le_mul hr (blocks3_one_le_r_sq hr) zero_le_one (le_trans zero_le_one hr)
      _ = r ^ 3 := by ring
  have hb4_nonneg := blocks3_b4_nonneg_of_ge_one hr
  have hb3sq : (blocks3SaddleB3Real r) ^ 2 ≤ (10 * r ^ 3) ^ 2 :=
    pow_le_pow_left₀ (blocks3_b3_nonneg_of_ge_one hr) (blocks3_b3_le hr) 2
  have hnum_le :
      (blocks3SaddleB3Real r) ^ 2 * blocks3SaddleB4Real r ≤ 2500 * r ^ 9 := by
    calc
      (blocks3SaddleB3Real r) ^ 2 * blocks3SaddleB4Real r
          ≤ (10 * r ^ 3) ^ 2 * (25 * r ^ 3) :=
            mul_le_mul hb3sq (blocks3_b4_le hr) hb4_nonneg (by positivity)
      _ = 2500 * r ^ 9 := by ring
  unfold blocks3ThirdCorrScale blocks3SecondCorrScale
  rw [blocks3_rpow_neg_three_eq_inv_cube hrpos]
  rw [abs_of_nonneg hb4_nonneg]
  calc
    (blocks3SaddleB3Real r) ^ 2 * blocks3SaddleB4Real r /
        (blocks3SaddleBReal r) ^ 5
        ≤ (2500 * r ^ 9) / r ^ 15 := by
          exact div_le_div₀ (by positivity) hnum_le (by positivity)
            (by nlinarith [hb5_ge])
    _ ≤ 100000 * (r ^ 3)⁻¹ := by
      field_simp [hrpos.ne']
      nlinarith [h1_le_r3, show 0 ≤ r ^ 12 by positivity]

private lemma blocks3_term_b3four_le_thirdCorrScale {r : ℝ} (hr : 1 ≤ r) :
    (blocks3SaddleB3Real r) ^ 4 / (blocks3SaddleBReal r) ^ 6 ≤
      100000 * blocks3ThirdCorrScale r := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hb6_ge := blocks3_b_pow_six_ge_r_pow_eighteen hr
  have h1_le_r3 : 1 ≤ r ^ 3 := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ r * r ^ 2 :=
        mul_le_mul hr (blocks3_one_le_r_sq hr) zero_le_one (le_trans zero_le_one hr)
      _ = r ^ 3 := by ring
  have hnum_le : (blocks3SaddleB3Real r) ^ 4 ≤ 10000 * r ^ 12 := by
    calc
      (blocks3SaddleB3Real r) ^ 4 ≤ (10 * r ^ 3) ^ 4 :=
        pow_le_pow_left₀ (blocks3_b3_nonneg_of_ge_one hr) (blocks3_b3_le hr) 4
      _ = 10000 * r ^ 12 := by ring
  unfold blocks3ThirdCorrScale blocks3SecondCorrScale
  rw [blocks3_rpow_neg_three_eq_inv_cube hrpos]
  calc
    (blocks3SaddleB3Real r) ^ 4 / (blocks3SaddleBReal r) ^ 6
        ≤ (10000 * r ^ 12) / r ^ 18 := by
          exact div_le_div₀ (by positivity) hnum_le (by positivity)
            (by nlinarith [hb6_ge])
    _ ≤ 100000 * (r ^ 3)⁻¹ := by
      field_simp [hrpos.ne']
      nlinarith [h1_le_r3, show 0 ≤ r ^ 15 by positivity]

lemma blocks3_saddleThirdCorrectionScale_le_thirdCorrScale :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ᶠ r : ℝ in atTop,
        saddleThirdCorrectionScale blocks3SaddleBReal blocks3SaddleB3Real
          blocks3SaddleB4Real blocks3SaddleB5Real blocks3SaddleB6Real r ≤
            K * blocks3ThirdCorrScale r := by
  refine ⟨2000000, by norm_num, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ),
      blocks3_saddleCorrectionScale_le_secondCorrScale_eventually] with r hr hsecond
  have hscale_nonneg : 0 ≤ blocks3ThirdCorrScale r := by
    unfold blocks3ThirdCorrScale blocks3SecondCorrScale
    positivity
  have hterm₁ := blocks3_term_b6_le_thirdCorrScale (r := r) hr
  have hterm₂ := blocks3_term_b3b5_le_thirdCorrScale (r := r) hr
  have hterm₃ := blocks3_term_b4sq_le_thirdCorrScale (r := r) hr
  have hterm₄ := blocks3_term_b3sqb4_le_thirdCorrScale (r := r) hr
  have hterm₅ := blocks3_term_b3four_le_thirdCorrScale (r := r) hr
  have hsecond' :
      saddleCorrectionScale blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real r
        ≤ 1000000 * blocks3ThirdCorrScale r := by
    simpa [blocks3ThirdCorrScale] using hsecond
  rw [saddleThirdCorrectionScale_apply]
  nlinarith

private def blocks3ThirdGaussianDom (x : ℝ) : ℝ :=
  Real.exp (-(x ^ 2) / 2) *
    (|x| ^ 5 + |x| ^ 6 + |x| ^ 7 + |x| ^ 8 +
      |x| ^ 9 + |x| ^ 10 + |x| ^ 12)

private lemma blocks3ThirdGaussianDom_nonneg (x : ℝ) :
    0 ≤ blocks3ThirdGaussianDom x := by
  unfold blocks3ThirdGaussianDom
  positivity

private lemma gaussian_abs_monomial_integrable_third (k : ℕ) :
    Integrable (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * |x| ^ k) := by
  have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Nat.zero_le k)
  have hk : (-1 : ℝ) < (k : ℝ) := by linarith
  have hbase : Integrable (fun x : ℝ => x ^ k * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) := by
    simpa [Real.rpow_natCast] using
      (integrable_rpow_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2) hk)
  have hbase2 : Integrable (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * x ^ k) := by
    convert hbase using 1
    ext x
    ring_nf
  have hnorm := hbase2.norm
  convert hnorm using 1
  ext x
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_pow]

private lemma blocks3ThirdGaussianDom_integrable : Integrable blocks3ThirdGaussianDom := by
  unfold blocks3ThirdGaussianDom
  have hsum :
      Integrable
        (((((fun x : ℝ => Real.exp (-(x ^ 2) / 2) * |x| ^ 5) +
          (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * |x| ^ 6)) +
          (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * |x| ^ 7)) +
          (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * |x| ^ 8)) +
          ((fun x : ℝ => Real.exp (-(x ^ 2) / 2) * |x| ^ 9) +
            (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * |x| ^ 10) +
            (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * |x| ^ 12))) :=
    ((((gaussian_abs_monomial_integrable_third 5).add
      (gaussian_abs_monomial_integrable_third 6)).add
      (gaussian_abs_monomial_integrable_third 7)).add
      (gaussian_abs_monomial_integrable_third 8)).add
      (((gaussian_abs_monomial_integrable_third 9).add
        (gaussian_abs_monomial_integrable_third 10)).add
        (gaussian_abs_monomial_integrable_third 12))
  convert hsum using 1
  ext x
  simp only [Pi.add_apply]
  ring_nf

private lemma blocks3ThirdGaussianDom_integral_nonneg :
    0 ≤ ∫ x : ℝ, blocks3ThirdGaussianDom x := by
  exact integral_nonneg (fun x => blocks3ThirdGaussianDom_nonneg x)

private lemma blocks3ThirdGaussianDom_continuous : Continuous blocks3ThirdGaussianDom := by
  unfold blocks3ThirdGaussianDom
  fun_prop

private lemma blocks3ThirdGaussianDom_window_le_integral {L : ℝ} (hL : 0 ≤ L) :
    (∫ x in -L..L, blocks3ThirdGaussianDom x) ≤ ∫ x : ℝ, blocks3ThirdGaussianDom x := by
  have hle : -L ≤ L := by linarith
  rw [intervalIntegral.integral_of_le hle]
  exact setIntegral_le_integral blocks3ThirdGaussianDom_integrable
    (Eventually.of_forall blocks3ThirdGaussianDom_nonneg)

private lemma blocks3_third_extra5_norm_le {r x : ℝ} (hr : 1 ≤ r) :
    ‖Complex.I * ((blocks3SaddleB5Real r : ℂ) /
      (120 * (Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 5)) * (x : ℂ) ^ 5‖ ≤
        10 * |x| ^ 5 / r ^ 4 := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hbpos : 0 < blocks3SaddleBReal r := blocks3SaddleBReal_pos_of_ge_one hr
  have hsqrt_pos : 0 < Real.sqrt (blocks3SaddleBReal r) := Real.sqrt_pos.mpr hbpos
  have hsqrt5_ge := blocks3_sqrtB_pow_five_ge_r_pow_seven hr
  have hcoef :
      ‖(blocks3SaddleB5Real r : ℂ) /
          (120 * (Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 5)‖ ≤ 10 / r ^ 4 := by
    calc
      ‖(blocks3SaddleB5Real r : ℂ) /
          (120 * (Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 5)‖
          = blocks3SaddleB5Real r /
              (120 * (Real.sqrt (blocks3SaddleBReal r)) ^ 5) := by
            rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (blocks3_b5_nonneg_of_ge_one hr)]
            simp only [norm_mul, Complex.norm_ofNat, norm_pow]
            rw [blocks3_sqrtB_norm_eq_of_ge_one hr]
      _ ≤ (60 * r ^ 3) / (120 * r ^ 7) := by
            exact div_le_div₀ (by positivity) (blocks3_b5_le hr) (by positivity)
              (by nlinarith [hsqrt5_ge])
      _ ≤ 10 / r ^ 4 := by
            field_simp [hrpos.ne']
            nlinarith [show 0 ≤ r ^ 7 by positivity]
  calc
    ‖Complex.I * ((blocks3SaddleB5Real r : ℂ) /
      (120 * (Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 5)) * (x : ℂ) ^ 5‖
        = ‖(blocks3SaddleB5Real r : ℂ) /
            (120 * (Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 5)‖ * |x| ^ 5 := by
          rw [norm_mul, norm_mul, norm_I, one_mul, norm_pow, Complex.norm_real,
            Real.norm_eq_abs]
    _ ≤ (10 / r ^ 4) * |x| ^ 5 :=
          mul_le_mul_of_nonneg_right hcoef (pow_nonneg (abs_nonneg x) 5)
    _ = 10 * |x| ^ 5 / r ^ 4 := by ring

private lemma blocks3_third_extra6_norm_le {r x : ℝ} (hr : 1 ≤ r) :
    ‖((blocks3SaddleB6Real r : ℂ) / (720 * (blocks3SaddleBReal r : ℂ) ^ 3)) *
        (x : ℂ) ^ 6‖ ≤ 10 * |x| ^ 6 / r ^ 4 := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hb3_ge := blocks3_b_pow_three_ge_r_pow_nine hr
  have h1_le_r2 := blocks3_one_le_r_sq hr
  have hcoef :
      ‖(blocks3SaddleB6Real r : ℂ) / (720 * (blocks3SaddleBReal r : ℂ) ^ 3)‖
        ≤ 10 / r ^ 4 := by
    calc
      ‖(blocks3SaddleB6Real r : ℂ) / (720 * (blocks3SaddleBReal r : ℂ) ^ 3)‖
          = blocks3SaddleB6Real r / (720 * (blocks3SaddleBReal r) ^ 3) := by
            rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (blocks3_b6_nonneg_of_ge_one hr)]
            simp only [norm_mul, Complex.norm_ofNat, norm_pow]
            rw [blocks3_b_norm_eq_of_ge_one hr]
      _ ≤ (160 * r ^ 3) / (720 * r ^ 9) := by
            exact div_le_div₀ (by positivity) (blocks3_b6_le hr) (by positivity)
              (by nlinarith [hb3_ge])
      _ ≤ 10 / r ^ 4 := by
            field_simp [hrpos.ne']
            nlinarith [h1_le_r2, show 0 ≤ r ^ 7 by positivity]
  calc
    ‖((blocks3SaddleB6Real r : ℂ) / (720 * (blocks3SaddleBReal r : ℂ) ^ 3)) *
        (x : ℂ) ^ 6‖
        = ‖(blocks3SaddleB6Real r : ℂ) /
            (720 * (blocks3SaddleBReal r : ℂ) ^ 3)‖ * |x| ^ 6 := by
          rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (10 / r ^ 4) * |x| ^ 6 :=
          mul_le_mul_of_nonneg_right hcoef (pow_nonneg (abs_nonneg x) 6)
    _ = 10 * |x| ^ 6 / r ^ 4 := by ring

private lemma blocks3_third_extra7_norm_le {r x : ℝ} (hr : 1 ≤ r) :
    ‖Complex.I * (((blocks3SaddleB3Real r * blocks3SaddleB4Real r : ℝ) : ℂ) /
      (144 * (Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 3 *
        (blocks3SaddleBReal r : ℂ) ^ 2)) * (x : ℂ) ^ 7‖ ≤
        10 * |x| ^ 7 / r ^ 4 := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hden_ge := blocks3_sqrtB_pow_three_mul_b_pow_two_ge_r_pow_ten hr
  have hnum_nonneg : 0 ≤ blocks3SaddleB3Real r * blocks3SaddleB4Real r :=
    mul_nonneg (blocks3_b3_nonneg_of_ge_one hr) (blocks3_b4_nonneg_of_ge_one hr)
  have hnum_le : blocks3SaddleB3Real r * blocks3SaddleB4Real r ≤ 250 * r ^ 6 := by
    calc
      blocks3SaddleB3Real r * blocks3SaddleB4Real r
          ≤ (10 * r ^ 3) * (25 * r ^ 3) :=
            mul_le_mul (blocks3_b3_le hr) (blocks3_b4_le hr)
              (blocks3_b4_nonneg_of_ge_one hr) (by positivity)
      _ = 250 * r ^ 6 := by ring
  have hcoef :
      ‖(((blocks3SaddleB3Real r * blocks3SaddleB4Real r : ℝ) : ℂ) /
        (144 * (Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 3 *
          (blocks3SaddleBReal r : ℂ) ^ 2))‖ ≤ 10 / r ^ 4 := by
    calc
      ‖(((blocks3SaddleB3Real r * blocks3SaddleB4Real r : ℝ) : ℂ) /
        (144 * (Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 3 *
          (blocks3SaddleBReal r : ℂ) ^ 2))‖
          =
            (blocks3SaddleB3Real r * blocks3SaddleB4Real r) /
              (144 * (Real.sqrt (blocks3SaddleBReal r)) ^ 3 *
                (blocks3SaddleBReal r) ^ 2) := by
            rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg hnum_nonneg]
            simp only [norm_mul, Complex.norm_ofNat, norm_pow]
            rw [blocks3_sqrtB_norm_eq_of_ge_one hr, blocks3_b_norm_eq_of_ge_one hr]
      _ ≤ (250 * r ^ 6) / (144 * r ^ 10) := by
            exact div_le_div₀ (by positivity) hnum_le (by positivity)
              (by nlinarith [hden_ge])
      _ ≤ 10 / r ^ 4 := by
            field_simp [hrpos.ne']
            nlinarith [show 0 ≤ r ^ 10 by positivity]
  calc
    ‖Complex.I * (((blocks3SaddleB3Real r * blocks3SaddleB4Real r : ℝ) : ℂ) /
      (144 * (Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 3 *
        (blocks3SaddleBReal r : ℂ) ^ 2)) * (x : ℂ) ^ 7‖
        = ‖(((blocks3SaddleB3Real r * blocks3SaddleB4Real r : ℝ) : ℂ) /
            (144 * (Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 3 *
              (blocks3SaddleBReal r : ℂ) ^ 2))‖ * |x| ^ 7 := by
          rw [norm_mul, norm_mul, norm_I, one_mul, norm_pow, Complex.norm_real,
            Real.norm_eq_abs]
    _ ≤ (10 / r ^ 4) * |x| ^ 7 :=
          mul_le_mul_of_nonneg_right hcoef (pow_nonneg (abs_nonneg x) 7)
    _ = 10 * |x| ^ 7 / r ^ 4 := by ring

private lemma blocks3_third_extra8a_norm_le {r x : ℝ} (hr : 1 ≤ r) :
    ‖(((blocks3SaddleB3Real r * blocks3SaddleB5Real r : ℝ) : ℂ) /
      (720 * (blocks3SaddleBReal r : ℂ) ^ 4)) * (x : ℂ) ^ 8‖ ≤
        10 * |x| ^ 8 / r ^ 4 := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hb4_ge := blocks3_b_pow_four_ge_r_pow_twelve hr
  have h1_le_r2 := blocks3_one_le_r_sq hr
  have hnum_nonneg : 0 ≤ blocks3SaddleB3Real r * blocks3SaddleB5Real r :=
    mul_nonneg (blocks3_b3_nonneg_of_ge_one hr) (blocks3_b5_nonneg_of_ge_one hr)
  have hnum_le : blocks3SaddleB3Real r * blocks3SaddleB5Real r ≤ 600 * r ^ 6 := by
    calc
      blocks3SaddleB3Real r * blocks3SaddleB5Real r
          ≤ (10 * r ^ 3) * (60 * r ^ 3) :=
            mul_le_mul (blocks3_b3_le hr) (blocks3_b5_le hr)
              (blocks3_b5_nonneg_of_ge_one hr) (by positivity)
      _ = 600 * r ^ 6 := by ring
  have hcoef :
      ‖(((blocks3SaddleB3Real r * blocks3SaddleB5Real r : ℝ) : ℂ) /
        (720 * (blocks3SaddleBReal r : ℂ) ^ 4))‖ ≤ 10 / r ^ 4 := by
    calc
      ‖(((blocks3SaddleB3Real r * blocks3SaddleB5Real r : ℝ) : ℂ) /
        (720 * (blocks3SaddleBReal r : ℂ) ^ 4))‖
          = (blocks3SaddleB3Real r * blocks3SaddleB5Real r) /
              (720 * (blocks3SaddleBReal r) ^ 4) := by
            rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg hnum_nonneg]
            simp only [norm_mul, Complex.norm_ofNat, norm_pow]
            rw [blocks3_b_norm_eq_of_ge_one hr]
      _ ≤ (600 * r ^ 6) / (720 * r ^ 12) := by
            exact div_le_div₀ (by positivity) hnum_le (by positivity)
              (by nlinarith [hb4_ge])
      _ ≤ 10 / r ^ 4 := by
            field_simp [hrpos.ne']
            nlinarith [h1_le_r2, show 0 ≤ r ^ 10 by positivity]
  calc
    ‖(((blocks3SaddleB3Real r * blocks3SaddleB5Real r : ℝ) : ℂ) /
      (720 * (blocks3SaddleBReal r : ℂ) ^ 4)) * (x : ℂ) ^ 8‖
        = ‖(((blocks3SaddleB3Real r * blocks3SaddleB5Real r : ℝ) : ℂ) /
            (720 * (blocks3SaddleBReal r : ℂ) ^ 4))‖ * |x| ^ 8 := by
          rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (10 / r ^ 4) * |x| ^ 8 :=
          mul_le_mul_of_nonneg_right hcoef (pow_nonneg (abs_nonneg x) 8)
    _ = 10 * |x| ^ 8 / r ^ 4 := by ring

private lemma blocks3_third_extra8b_norm_le {r x : ℝ} (hr : 1 ≤ r) :
    ‖((((blocks3SaddleB4Real r) ^ 2 : ℝ) : ℂ) /
      (1152 * (blocks3SaddleBReal r : ℂ) ^ 4)) * (x : ℂ) ^ 8‖ ≤
        10 * |x| ^ 8 / r ^ 4 := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hb4_ge := blocks3_b_pow_four_ge_r_pow_twelve hr
  have h1_le_r2 := blocks3_one_le_r_sq hr
  have hnum_le : (blocks3SaddleB4Real r) ^ 2 ≤ 625 * r ^ 6 := by
    calc
      (blocks3SaddleB4Real r) ^ 2 ≤ (25 * r ^ 3) ^ 2 :=
        pow_le_pow_left₀ (blocks3_b4_nonneg_of_ge_one hr) (blocks3_b4_le hr) 2
      _ = 625 * r ^ 6 := by ring
  have hcoef :
      ‖((((blocks3SaddleB4Real r) ^ 2 : ℝ) : ℂ) /
        (1152 * (blocks3SaddleBReal r : ℂ) ^ 4))‖ ≤ 10 / r ^ 4 := by
    calc
      ‖((((blocks3SaddleB4Real r) ^ 2 : ℝ) : ℂ) /
        (1152 * (blocks3SaddleBReal r : ℂ) ^ 4))‖
          = (blocks3SaddleB4Real r) ^ 2 / (1152 * (blocks3SaddleBReal r) ^ 4) := by
            rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (sq_nonneg _)]
            simp only [norm_mul, Complex.norm_ofNat, norm_pow]
            rw [blocks3_b_norm_eq_of_ge_one hr]
      _ ≤ (625 * r ^ 6) / (1152 * r ^ 12) := by
            exact div_le_div₀ (by positivity) hnum_le (by positivity)
              (by nlinarith [hb4_ge])
      _ ≤ 10 / r ^ 4 := by
            field_simp [hrpos.ne']
            nlinarith [h1_le_r2, show 0 ≤ r ^ 10 by positivity]
  calc
    ‖((((blocks3SaddleB4Real r) ^ 2 : ℝ) : ℂ) /
      (1152 * (blocks3SaddleBReal r : ℂ) ^ 4)) * (x : ℂ) ^ 8‖
        = ‖((((blocks3SaddleB4Real r) ^ 2 : ℝ) : ℂ) /
            (1152 * (blocks3SaddleBReal r : ℂ) ^ 4))‖ * |x| ^ 8 := by
          rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (10 / r ^ 4) * |x| ^ 8 :=
          mul_le_mul_of_nonneg_right hcoef (pow_nonneg (abs_nonneg x) 8)
    _ = 10 * |x| ^ 8 / r ^ 4 := by ring

private lemma blocks3_third_extra9_norm_le {r x : ℝ} (hr : 1 ≤ r) :
    ‖Complex.I * ((((blocks3SaddleB3Real r) ^ 3 : ℝ) : ℂ) /
      (1296 * (Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 9)) * (x : ℂ) ^ 9‖ ≤
        10 * |x| ^ 9 / r ^ 4 := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hsqrt9_ge := blocks3_sqrtB_pow_nine_ge_r_pow_thirteen hr
  have hnum_le : (blocks3SaddleB3Real r) ^ 3 ≤ 1000 * r ^ 9 := by
    calc
      (blocks3SaddleB3Real r) ^ 3 ≤ (10 * r ^ 3) ^ 3 :=
        pow_le_pow_left₀ (blocks3_b3_nonneg_of_ge_one hr) (blocks3_b3_le hr) 3
      _ = 1000 * r ^ 9 := by ring
  have hcoef :
      ‖((((blocks3SaddleB3Real r) ^ 3 : ℝ) : ℂ) /
        (1296 * (Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 9))‖ ≤ 10 / r ^ 4 := by
    calc
      ‖((((blocks3SaddleB3Real r) ^ 3 : ℝ) : ℂ) /
        (1296 * (Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 9))‖
          = (blocks3SaddleB3Real r) ^ 3 /
              (1296 * (Real.sqrt (blocks3SaddleBReal r)) ^ 9) := by
            rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (pow_nonneg (blocks3_b3_nonneg_of_ge_one hr) 3)]
            simp only [norm_mul, Complex.norm_ofNat, norm_pow]
            rw [blocks3_sqrtB_norm_eq_of_ge_one hr]
      _ ≤ (1000 * r ^ 9) / (1296 * r ^ 13) := by
            exact div_le_div₀ (by positivity) hnum_le (by positivity)
              (by nlinarith [hsqrt9_ge])
      _ ≤ 10 / r ^ 4 := by
            field_simp [hrpos.ne']
            nlinarith [show 0 ≤ r ^ 13 by positivity]
  calc
    ‖Complex.I * ((((blocks3SaddleB3Real r) ^ 3 : ℝ) : ℂ) /
      (1296 * (Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 9)) * (x : ℂ) ^ 9‖
        = ‖((((blocks3SaddleB3Real r) ^ 3 : ℝ) : ℂ) /
            (1296 * (Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 9))‖ * |x| ^ 9 := by
          rw [norm_mul, norm_mul, norm_I, one_mul, norm_pow, Complex.norm_real,
            Real.norm_eq_abs]
    _ ≤ (10 / r ^ 4) * |x| ^ 9 :=
          mul_le_mul_of_nonneg_right hcoef (pow_nonneg (abs_nonneg x) 9)
    _ = 10 * |x| ^ 9 / r ^ 4 := by ring

private lemma blocks3_third_extra10_norm_le {r x : ℝ} (hr : 1 ≤ r) :
    ‖(((((blocks3SaddleB3Real r) ^ 2 * blocks3SaddleB4Real r : ℝ) : ℂ) /
      (1728 * (blocks3SaddleBReal r : ℂ) ^ 5)) * (x : ℂ) ^ 10)‖ ≤
        10 * |x| ^ 10 / r ^ 4 := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hb5_ge := blocks3_b_pow_five_ge_r_pow_fifteen hr
  have h1_le_r2 := blocks3_one_le_r_sq hr
  have hb3sq : (blocks3SaddleB3Real r) ^ 2 ≤ (10 * r ^ 3) ^ 2 :=
    pow_le_pow_left₀ (blocks3_b3_nonneg_of_ge_one hr) (blocks3_b3_le hr) 2
  have hnum_nonneg : 0 ≤ (blocks3SaddleB3Real r) ^ 2 * blocks3SaddleB4Real r :=
    mul_nonneg (sq_nonneg _) (blocks3_b4_nonneg_of_ge_one hr)
  have hnum_le :
      (blocks3SaddleB3Real r) ^ 2 * blocks3SaddleB4Real r ≤ 2500 * r ^ 9 := by
    calc
      (blocks3SaddleB3Real r) ^ 2 * blocks3SaddleB4Real r
          ≤ (10 * r ^ 3) ^ 2 * (25 * r ^ 3) :=
            mul_le_mul hb3sq (blocks3_b4_le hr)
              (blocks3_b4_nonneg_of_ge_one hr) (by positivity)
      _ = 2500 * r ^ 9 := by ring
  have hcoef :
      ‖(((((blocks3SaddleB3Real r) ^ 2 * blocks3SaddleB4Real r : ℝ) : ℂ) /
        (1728 * (blocks3SaddleBReal r : ℂ) ^ 5)))‖ ≤ 10 / r ^ 4 := by
    calc
      ‖(((((blocks3SaddleB3Real r) ^ 2 * blocks3SaddleB4Real r : ℝ) : ℂ) /
        (1728 * (blocks3SaddleBReal r : ℂ) ^ 5)))‖
          = ((blocks3SaddleB3Real r) ^ 2 * blocks3SaddleB4Real r) /
              (1728 * (blocks3SaddleBReal r) ^ 5) := by
            rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg hnum_nonneg]
            simp only [norm_mul, Complex.norm_ofNat, norm_pow]
            rw [blocks3_b_norm_eq_of_ge_one hr]
      _ ≤ (2500 * r ^ 9) / (1728 * r ^ 15) := by
            exact div_le_div₀ (by positivity) hnum_le (by positivity)
              (by nlinarith [hb5_ge])
      _ ≤ 10 / r ^ 4 := by
            field_simp [hrpos.ne']
            nlinarith [h1_le_r2, show 0 ≤ r ^ 13 by positivity]
  calc
    ‖(((((blocks3SaddleB3Real r) ^ 2 * blocks3SaddleB4Real r : ℝ) : ℂ) /
      (1728 * (blocks3SaddleBReal r : ℂ) ^ 5)) * (x : ℂ) ^ 10)‖
        = ‖(((((blocks3SaddleB3Real r) ^ 2 * blocks3SaddleB4Real r : ℝ) : ℂ) /
            (1728 * (blocks3SaddleBReal r : ℂ) ^ 5)))‖ * |x| ^ 10 := by
          rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (10 / r ^ 4) * |x| ^ 10 :=
          mul_le_mul_of_nonneg_right hcoef (pow_nonneg (abs_nonneg x) 10)
    _ = 10 * |x| ^ 10 / r ^ 4 := by ring

private lemma blocks3_third_extra12_norm_le {r x : ℝ} (hr : 1 ≤ r) :
    ‖((((blocks3SaddleB3Real r) ^ 4 : ℝ) : ℂ) /
      (31104 * (blocks3SaddleBReal r : ℂ) ^ 6)) * (x : ℂ) ^ 12‖ ≤
        10 * |x| ^ 12 / r ^ 4 := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hb6_ge := blocks3_b_pow_six_ge_r_pow_eighteen hr
  have h1_le_r2 := blocks3_one_le_r_sq hr
  have hnum_le : (blocks3SaddleB3Real r) ^ 4 ≤ 10000 * r ^ 12 := by
    calc
      (blocks3SaddleB3Real r) ^ 4 ≤ (10 * r ^ 3) ^ 4 :=
        pow_le_pow_left₀ (blocks3_b3_nonneg_of_ge_one hr) (blocks3_b3_le hr) 4
      _ = 10000 * r ^ 12 := by ring
  have hcoef :
      ‖((((blocks3SaddleB3Real r) ^ 4 : ℝ) : ℂ) /
        (31104 * (blocks3SaddleBReal r : ℂ) ^ 6))‖ ≤ 10 / r ^ 4 := by
    calc
      ‖((((blocks3SaddleB3Real r) ^ 4 : ℝ) : ℂ) /
        (31104 * (blocks3SaddleBReal r : ℂ) ^ 6))‖
          = (blocks3SaddleB3Real r) ^ 4 / (31104 * (blocks3SaddleBReal r) ^ 6) := by
            rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (pow_nonneg (blocks3_b3_nonneg_of_ge_one hr) 4)]
            simp only [norm_mul, Complex.norm_ofNat, norm_pow]
            rw [blocks3_b_norm_eq_of_ge_one hr]
      _ ≤ (10000 * r ^ 12) / (31104 * r ^ 18) := by
            exact div_le_div₀ (by positivity) hnum_le (by positivity)
              (by nlinarith [hb6_ge])
      _ ≤ 10 / r ^ 4 := by
            field_simp [hrpos.ne']
            nlinarith [h1_le_r2, show 0 ≤ r ^ 16 by positivity]
  calc
    ‖((((blocks3SaddleB3Real r) ^ 4 : ℝ) : ℂ) /
      (31104 * (blocks3SaddleBReal r : ℂ) ^ 6)) * (x : ℂ) ^ 12‖
        = ‖((((blocks3SaddleB3Real r) ^ 4 : ℝ) : ℂ) /
            (31104 * (blocks3SaddleBReal r : ℂ) ^ 6))‖ * |x| ^ 12 := by
          rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (10 / r ^ 4) * |x| ^ 12 :=
          mul_le_mul_of_nonneg_right hcoef (pow_nonneg (abs_nonneg x) 12)
    _ = 10 * |x| ^ 12 / r ^ 4 := by ring

private lemma norm_add8_le (z1 z2 z3 z4 z5 z6 z7 z8 : ℂ) :
    ‖z1 + z2 + z3 + z4 + z5 + z6 + z7 + z8‖ ≤
      ‖z1‖ + ‖z2‖ + ‖z3‖ + ‖z4‖ + ‖z5‖ + ‖z6‖ + ‖z7‖ + ‖z8‖ := by
  have h1 : ‖z1 + z2 + z3 + z4 + z5 + z6 + z7 + z8‖ ≤
      ‖z1‖ + ‖z2 + z3 + z4 + z5 + z6 + z7 + z8‖ := by
    simpa [add_assoc] using norm_add_le z1 (z2 + z3 + z4 + z5 + z6 + z7 + z8)
  have h2 : ‖z2 + z3 + z4 + z5 + z6 + z7 + z8‖ ≤
      ‖z2‖ + ‖z3 + z4 + z5 + z6 + z7 + z8‖ := by
    simpa [add_assoc] using norm_add_le z2 (z3 + z4 + z5 + z6 + z7 + z8)
  have h3 : ‖z3 + z4 + z5 + z6 + z7 + z8‖ ≤
      ‖z3‖ + ‖z4 + z5 + z6 + z7 + z8‖ := by
    simpa [add_assoc] using norm_add_le z3 (z4 + z5 + z6 + z7 + z8)
  have h4 : ‖z4 + z5 + z6 + z7 + z8‖ ≤
      ‖z4‖ + ‖z5 + z6 + z7 + z8‖ := by
    simpa [add_assoc] using norm_add_le z4 (z5 + z6 + z7 + z8)
  have h5 : ‖z5 + z6 + z7 + z8‖ ≤ ‖z5‖ + ‖z6 + z7 + z8‖ := by
    simpa [add_assoc] using norm_add_le z5 (z6 + z7 + z8)
  have h6 : ‖z6 + z7 + z8‖ ≤ ‖z6‖ + ‖z7 + z8‖ := by
    simpa [add_assoc] using norm_add_le z6 (z7 + z8)
  have h7 : ‖z7 + z8‖ ≤ ‖z7‖ + ‖z8‖ := norm_add_le z7 z8
  nlinarith

private lemma blocks3_third_extra_norm_le {r x : ℝ} (hr : 1 ≤ r) :
    ‖saddleThirdPoly blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real
        blocks3SaddleB5Real blocks3SaddleB6Real r x -
      saddleSecondPoly blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real r x‖
      ≤ 1000 * (|x| ^ 5 + |x| ^ 6 + |x| ^ 7 + |x| ^ 8 +
        |x| ^ 9 + |x| ^ 10 + |x| ^ 12) / r ^ 4 := by
  let T5 : ℂ :=
    Complex.I * ((blocks3SaddleB5Real r : ℂ) /
      (120 * (Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 5)) * (x : ℂ) ^ 5
  let T6 : ℂ :=
    -((blocks3SaddleB6Real r : ℂ) / (720 * (blocks3SaddleBReal r : ℂ) ^ 3)) *
      (x : ℂ) ^ 6
  let T7 : ℂ :=
    -Complex.I * (((blocks3SaddleB3Real r * blocks3SaddleB4Real r : ℝ) : ℂ) /
      (144 * (Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 3 *
        (blocks3SaddleBReal r : ℂ) ^ 2)) * (x : ℂ) ^ 7
  let T8a : ℂ :=
    (((blocks3SaddleB3Real r * blocks3SaddleB5Real r : ℝ) : ℂ) /
      (720 * (blocks3SaddleBReal r : ℂ) ^ 4)) * (x : ℂ) ^ 8
  let T8b : ℂ :=
    ((((blocks3SaddleB4Real r) ^ 2 : ℝ) : ℂ) /
      (1152 * (blocks3SaddleBReal r : ℂ) ^ 4)) * (x : ℂ) ^ 8
  let T9 : ℂ :=
    Complex.I * ((((blocks3SaddleB3Real r) ^ 3 : ℝ) : ℂ) /
      (1296 * (Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 9)) * (x : ℂ) ^ 9
  let T10 : ℂ :=
    -(((((blocks3SaddleB3Real r) ^ 2 * blocks3SaddleB4Real r : ℝ) : ℂ) /
      (1728 * (blocks3SaddleBReal r : ℂ) ^ 5)) * (x : ℂ) ^ 10)
  let T12 : ℂ :=
    ((((blocks3SaddleB3Real r) ^ 4 : ℝ) : ℂ) /
      (31104 * (blocks3SaddleBReal r : ℂ) ^ 6)) * (x : ℂ) ^ 12
  have h5 : ‖T5‖ ≤ 10 * |x| ^ 5 / r ^ 4 := by
    dsimp [T5]
    exact blocks3_third_extra5_norm_le (r := r) (x := x) hr
  have h6 : ‖T6‖ ≤ 10 * |x| ^ 6 / r ^ 4 := by
    dsimp [T6]
    simpa using blocks3_third_extra6_norm_le (r := r) (x := x) hr
  have h7 : ‖T7‖ ≤ 10 * |x| ^ 7 / r ^ 4 := by
    dsimp [T7]
    simpa [norm_neg] using blocks3_third_extra7_norm_le (r := r) (x := x) hr
  have h8a : ‖T8a‖ ≤ 10 * |x| ^ 8 / r ^ 4 := by
    dsimp [T8a]
    exact blocks3_third_extra8a_norm_le (r := r) (x := x) hr
  have h8b : ‖T8b‖ ≤ 10 * |x| ^ 8 / r ^ 4 := by
    dsimp [T8b]
    exact blocks3_third_extra8b_norm_le (r := r) (x := x) hr
  have h9 : ‖T9‖ ≤ 10 * |x| ^ 9 / r ^ 4 := by
    dsimp [T9]
    exact blocks3_third_extra9_norm_le (r := r) (x := x) hr
  have h10 : ‖T10‖ ≤ 10 * |x| ^ 10 / r ^ 4 := by
    dsimp [T10]
    simpa [norm_neg] using blocks3_third_extra10_norm_le (r := r) (x := x) hr
  have h12 : ‖T12‖ ≤ 10 * |x| ^ 12 / r ^ 4 := by
    dsimp [T12]
    exact blocks3_third_extra12_norm_le (r := r) (x := x) hr
  have hdiff :
      saddleThirdPoly blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real
          blocks3SaddleB5Real blocks3SaddleB6Real r x -
        saddleSecondPoly blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real r x =
        T5 + T6 + T7 + T8a + T8b + T9 + T10 + T12 := by
    dsimp [T5, T6, T7, T8a, T8b, T9, T10, T12]
    ring
  have hnonneg : 0 ≤ |x| ^ 5 + |x| ^ 6 + |x| ^ 7 + |x| ^ 8 +
      |x| ^ 9 + |x| ^ 10 + |x| ^ 12 := by positivity
  rw [hdiff]
  calc
    ‖T5 + T6 + T7 + T8a + T8b + T9 + T10 + T12‖
        ≤ ‖T5‖ + ‖T6‖ + ‖T7‖ + ‖T8a‖ + ‖T8b‖ + ‖T9‖ + ‖T10‖ + ‖T12‖ :=
          norm_add8_le T5 T6 T7 T8a T8b T9 T10 T12
    _ ≤ 10 * |x| ^ 5 / r ^ 4 + 10 * |x| ^ 6 / r ^ 4 +
          10 * |x| ^ 7 / r ^ 4 + 10 * |x| ^ 8 / r ^ 4 +
          10 * |x| ^ 8 / r ^ 4 + 10 * |x| ^ 9 / r ^ 4 +
          10 * |x| ^ 10 / r ^ 4 + 10 * |x| ^ 12 / r ^ 4 := by
          nlinarith
    _ ≤ 1000 * (|x| ^ 5 + |x| ^ 6 + |x| ^ 7 + |x| ^ 8 +
          |x| ^ 9 + |x| ^ 10 + |x| ^ 12) / r ^ 4 := by
          have hr4pos : 0 < r ^ 4 := by positivity
          field_simp [hr4pos.ne']
          nlinarith [hnonneg, pow_nonneg (abs_nonneg x) 5,
            pow_nonneg (abs_nonneg x) 6, pow_nonneg (abs_nonneg x) 7,
            pow_nonneg (abs_nonneg x) 8, pow_nonneg (abs_nonneg x) 9,
            pow_nonneg (abs_nonneg x) 10, pow_nonneg (abs_nonneg x) 12]

private lemma blocks3_local_third_extra_L1 :
    Tendsto
      (fun r : ℝ =>
        (∫ x in -(blocks3SaddleDeltaReal r * Real.sqrt (blocks3SaddleBReal r))..
          (blocks3SaddleDeltaReal r * Real.sqrt (blocks3SaddleBReal r)),
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleThirdPoly blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real
              blocks3SaddleB5Real blocks3SaddleB6Real r x -
              saddleSecondPoly blocks3SaddleBReal blocks3SaddleB3Real
                blocks3SaddleB4Real r x)‖) /
          blocks3SecondCorrScale r)
      atTop (𝓝 0) := by
  let M : ℝ := ∫ x : ℝ, blocks3ThirdGaussianDom x
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact blocks3ThirdGaussianDom_integral_nonneg
  have hupper_tendsto :
      Tendsto (fun r : ℝ => (1000 * M) / r) atTop (𝓝 0) := by
    have hinv : Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero
    simpa [div_eq_mul_inv, mul_assoc] using hinv.const_mul (1000 * M)
  refine squeeze_zero' ?_ ?_ hupper_tendsto
  · filter_upwards [eventually_ge_atTop (1 : ℝ), blocks3SecondCorrScale_pos_eventually] with
      r hr hcorr
    let L : ℝ := blocks3SaddleDeltaReal r * Real.sqrt (blocks3SaddleBReal r)
    have hLnonneg : 0 ≤ L := by
      dsimp [L, blocks3SaddleDeltaReal]
      positivity
    have hle : -L ≤ L := by linarith
    have hint_nonneg :
        0 ≤ ∫ x in -L..L,
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleThirdPoly blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real
              blocks3SaddleB5Real blocks3SaddleB6Real r x -
              saddleSecondPoly blocks3SaddleBReal blocks3SaddleB3Real
                blocks3SaddleB4Real r x)‖ :=
      intervalIntegral.integral_nonneg hle (fun _ _ => norm_nonneg _)
    exact div_nonneg hint_nonneg hcorr.le
  · filter_upwards [eventually_ge_atTop (1 : ℝ), blocks3SecondCorrScale_pos_eventually] with
      r hr hcorrPos
    let L : ℝ := blocks3SaddleDeltaReal r * Real.sqrt (blocks3SaddleBReal r)
    let F : ℝ → ℝ := fun x =>
      ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleThirdPoly blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real
          blocks3SaddleB5Real blocks3SaddleB6Real r x -
          saddleSecondPoly blocks3SaddleBReal blocks3SaddleB3Real
            blocks3SaddleB4Real r x)‖
    let G : ℝ → ℝ := fun x => (1000 / r ^ 4) * blocks3ThirdGaussianDom x
    have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
    have hLnonneg : 0 ≤ L := by
      dsimp [L, blocks3SaddleDeltaReal]
      positivity
    have hle : -L ≤ L := by linarith
    have hpoint : ∀ x ∈ Set.Icc (-L) L, F x ≤ G x := by
      intro x hx
      have hdiff := blocks3_third_extra_norm_le (r := r) (x := x) hr
      dsimp [F, G, blocks3ThirdGaussianDom]
      rw [norm_mul]
      have hgauss :
          ‖Complex.exp (-(x ^ 2) / 2)‖ = Real.exp (-(x ^ 2) / 2) := by
        rw [Complex.norm_exp]
        congr 1
        simp [pow_two]
      rw [hgauss]
      calc
        Real.exp (-(x ^ 2) / 2) *
            ‖saddleThirdPoly blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real
                blocks3SaddleB5Real blocks3SaddleB6Real r x -
              saddleSecondPoly blocks3SaddleBReal blocks3SaddleB3Real
                blocks3SaddleB4Real r x‖
            ≤ Real.exp (-(x ^ 2) / 2) *
                (1000 * (|x| ^ 5 + |x| ^ 6 + |x| ^ 7 + |x| ^ 8 +
                  |x| ^ 9 + |x| ^ 10 + |x| ^ 12) / r ^ 4) :=
              mul_le_mul_of_nonneg_left hdiff (Real.exp_pos _).le
        _ = 1000 / r ^ 4 *
            (Real.exp (-(x ^ 2) / 2) *
              (|x| ^ 5 + |x| ^ 6 + |x| ^ 7 + |x| ^ 8 +
                |x| ^ 9 + |x| ^ 10 + |x| ^ 12)) := by ring
    have hFint : IntervalIntegrable F volume (-L) L := by
      have hcont : Continuous F := by
        dsimp [F]
        simp only [saddleThirdPoly, saddleSecondPoly, blocks3SaddleBReal,
          blocks3SaddleB3Real, blocks3SaddleB4Real, blocks3SaddleB5Real,
          blocks3SaddleB6Real]
        fun_prop
      exact hcont.intervalIntegrable _ _
    have hGint : IntervalIntegrable G volume (-L) L := by
      exact (blocks3ThirdGaussianDom_continuous.const_mul (1000 / r ^ 4)).intervalIntegrable _ _
    have hIntBound :
        (∫ x in -L..L, F x) ≤ (1000 / r ^ 4) * M := by
      calc
        (∫ x in -L..L, F x) ≤ ∫ x in -L..L, G x :=
          intervalIntegral.integral_mono_on hle hFint hGint hpoint
        _ = (1000 / r ^ 4) * (∫ x in -L..L, blocks3ThirdGaussianDom x) := by
          dsimp [G]
          rw [intervalIntegral.integral_const_mul]
        _ ≤ (1000 / r ^ 4) * M := by
          exact mul_le_mul_of_nonneg_left
            (by dsimp [M]; exact blocks3ThirdGaussianDom_window_le_integral hLnonneg)
            (div_nonneg (by norm_num) (by positivity))
    have hnum_nonneg : 0 ≤ (1000 / r ^ 4) * M :=
      mul_nonneg (div_nonneg (by norm_num) (by positivity)) hM_nonneg
    have hmain :
        (∫ x in -L..L, F x) / blocks3SecondCorrScale r ≤
          ((1000 / r ^ 4) * M) / blocks3SecondCorrScale r :=
      div_le_div_of_nonneg_right hIntBound hcorrPos.le
    calc
      ((∫ x in -(blocks3SaddleDeltaReal r * Real.sqrt (blocks3SaddleBReal r))..
          (blocks3SaddleDeltaReal r * Real.sqrt (blocks3SaddleBReal r)),
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleThirdPoly blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real
              blocks3SaddleB5Real blocks3SaddleB6Real r x -
              saddleSecondPoly blocks3SaddleBReal blocks3SaddleB3Real
                blocks3SaddleB4Real r x)‖) /
          blocks3SecondCorrScale r)
          = (∫ x in -L..L, F x) / blocks3SecondCorrScale r := by rfl
      _ ≤ ((1000 / r ^ 4) * M) / blocks3SecondCorrScale r := hmain
      _ = (1000 * M) / r := by
        unfold blocks3SecondCorrScale
        rw [Real.rpow_neg hrpos.le]
        rw [show r ^ (3 : ℝ) = r ^ 3 by exact Real.rpow_natCast r 3]
        field_simp [hrpos.ne']

theorem blocks3_local_third_L1 :
    Tendsto
      (fun r : ℝ =>
        (∫ x in -(blocks3SaddleDeltaReal r * Real.sqrt (blocks3SaddleBReal r))..
          (blocks3SaddleDeltaReal r * Real.sqrt (blocks3SaddleBReal r)),
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleLocalRatio blocks3Fun blocks3SaddleAReal blocks3SaddleBReal r
                (x / Real.sqrt (blocks3SaddleBReal r)) -
              saddleThirdPoly blocks3SaddleBReal blocks3SaddleB3Real
                blocks3SaddleB4Real blocks3SaddleB5Real blocks3SaddleB6Real r x)‖) /
          blocks3ThirdCorrScale r)
      atTop (𝓝 0) := by
  unfold blocks3ThirdCorrScale
  let T : ℝ → ℝ := fun r =>
    (∫ x in -(blocks3SaddleDeltaReal r * Real.sqrt (blocks3SaddleBReal r))..
      (blocks3SaddleDeltaReal r * Real.sqrt (blocks3SaddleBReal r)),
      ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleLocalRatio blocks3Fun blocks3SaddleAReal blocks3SaddleBReal r
            (x / Real.sqrt (blocks3SaddleBReal r)) -
          saddleThirdPoly blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real
            blocks3SaddleB5Real blocks3SaddleB6Real r x)‖) / blocks3SecondCorrScale r
  let S : ℝ → ℝ := fun r =>
    (∫ x in -(blocks3SaddleDeltaReal r * Real.sqrt (blocks3SaddleBReal r))..
      (blocks3SaddleDeltaReal r * Real.sqrt (blocks3SaddleBReal r)),
      ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleLocalRatio blocks3Fun blocks3SaddleAReal blocks3SaddleBReal r
            (x / Real.sqrt (blocks3SaddleBReal r)) -
          saddleSecondPoly blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real r x)‖) /
      blocks3SecondCorrScale r
  let E : ℝ → ℝ := fun r =>
    (∫ x in -(blocks3SaddleDeltaReal r * Real.sqrt (blocks3SaddleBReal r))..
      (blocks3SaddleDeltaReal r * Real.sqrt (blocks3SaddleBReal r)),
      ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleThirdPoly blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real
          blocks3SaddleB5Real blocks3SaddleB6Real r x -
          saddleSecondPoly blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real r x)‖) /
      blocks3SecondCorrScale r
  change Tendsto T atTop (𝓝 0)
  have hsecond := blocks3_local_second_L1
  have hextra := blocks3_local_third_extra_L1
  have hsum : Tendsto (fun r : ℝ => S r + E r) atTop (𝓝 0) := by
    simpa [S, E] using hsecond.add hextra
  refine squeeze_zero' ?_ ?_ hsum
  · filter_upwards [eventually_ge_atTop (1 : ℝ), blocks3SecondCorrScale_pos_eventually] with
      r hr hcorr
    let L : ℝ := blocks3SaddleDeltaReal r * Real.sqrt (blocks3SaddleBReal r)
    have hLnonneg : 0 ≤ L := by
      dsimp [L, blocks3SaddleDeltaReal]
      positivity
    have hle : -L ≤ L := by linarith
    have hint_nonneg :
        0 ≤ ∫ x in -L..L,
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleLocalRatio blocks3Fun blocks3SaddleAReal blocks3SaddleBReal r
                (x / Real.sqrt (blocks3SaddleBReal r)) -
              saddleThirdPoly blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real
                blocks3SaddleB5Real blocks3SaddleB6Real r x)‖ :=
      intervalIntegral.integral_nonneg hle (fun _ _ => norm_nonneg _)
    dsimp [T]
    exact div_nonneg hint_nonneg hcorr.le
  · filter_upwards [eventually_ge_atTop (1 : ℝ), blocks3SecondCorrScale_pos_eventually] with
      r hr hcorr
    let L : ℝ := blocks3SaddleDeltaReal r * Real.sqrt (blocks3SaddleBReal r)
    let FT : ℝ → ℝ := fun x =>
      ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleLocalRatio blocks3Fun blocks3SaddleAReal blocks3SaddleBReal r
            (x / Real.sqrt (blocks3SaddleBReal r)) -
          saddleThirdPoly blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real
            blocks3SaddleB5Real blocks3SaddleB6Real r x)‖
    let FS : ℝ → ℝ := fun x =>
      ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleLocalRatio blocks3Fun blocks3SaddleAReal blocks3SaddleBReal r
            (x / Real.sqrt (blocks3SaddleBReal r)) -
          saddleSecondPoly blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real r x)‖
    let FE : ℝ → ℝ := fun x =>
      ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleThirdPoly blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real
          blocks3SaddleB5Real blocks3SaddleB6Real r x -
          saddleSecondPoly blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real r x)‖
    have hLnonneg : 0 ≤ L := by
      dsimp [L, blocks3SaddleDeltaReal]
      positivity
    have hle : -L ≤ L := by linarith
    have hpoint : ∀ x ∈ Set.Icc (-L) L, FT x ≤ FS x + FE x := by
      intro x hx
      dsimp [FT, FS, FE]
      calc
        ‖Complex.exp (-(x ^ 2) / 2) *
          (saddleLocalRatio blocks3Fun blocks3SaddleAReal blocks3SaddleBReal r
              (x / Real.sqrt (blocks3SaddleBReal r)) -
            saddleThirdPoly blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real
              blocks3SaddleB5Real blocks3SaddleB6Real r x)‖
            =
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleLocalRatio blocks3Fun blocks3SaddleAReal blocks3SaddleBReal r
                (x / Real.sqrt (blocks3SaddleBReal r)) -
              saddleSecondPoly blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real r x) -
            Complex.exp (-(x ^ 2) / 2) *
              (saddleThirdPoly blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real
                blocks3SaddleB5Real blocks3SaddleB6Real r x -
                saddleSecondPoly blocks3SaddleBReal blocks3SaddleB3Real
                  blocks3SaddleB4Real r x)‖ := by
              congr 1
              ring
        _ ≤
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleLocalRatio blocks3Fun blocks3SaddleAReal blocks3SaddleBReal r
                (x / Real.sqrt (blocks3SaddleBReal r)) -
              saddleSecondPoly blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real r x)‖ +
          ‖Complex.exp (-(x ^ 2) / 2) *
              (saddleThirdPoly blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real
                blocks3SaddleB5Real blocks3SaddleB6Real r x -
                saddleSecondPoly blocks3SaddleBReal blocks3SaddleB3Real
                  blocks3SaddleB4Real r x)‖ :=
            norm_sub_le _ _
    have hFTint : IntervalIntegrable FT volume (-L) L := by
      have hcont : Continuous FT := by
        dsimp [FT]
        simp only [blocks3_saddleLocalRatio_eq]
        simp only [saddleThirdPoly, saddleSecondPoly, blocks3LocalExponent,
          ExpStirling.expLocalRemainder, blocks3Fun, blocks3SaddleAReal,
          blocks3SaddleBReal, blocks3SaddleB3Real, blocks3SaddleB4Real,
          blocks3SaddleB5Real, blocks3SaddleB6Real]
        fun_prop
      exact hcont.intervalIntegrable _ _
    have hFSint : IntervalIntegrable FS volume (-L) L := by
      have hcont : Continuous FS := by
        dsimp [FS]
        simp only [blocks3_saddleLocalRatio_eq]
        simp only [saddleSecondPoly, blocks3LocalExponent, ExpStirling.expLocalRemainder,
          blocks3Fun, blocks3SaddleAReal, blocks3SaddleBReal, blocks3SaddleB3Real,
          blocks3SaddleB4Real]
        fun_prop
      exact hcont.intervalIntegrable _ _
    have hFEint : IntervalIntegrable FE volume (-L) L := by
      have hcont : Continuous FE := by
        dsimp [FE]
        simp only [saddleThirdPoly, saddleSecondPoly, blocks3SaddleBReal, blocks3SaddleB3Real,
          blocks3SaddleB4Real, blocks3SaddleB5Real, blocks3SaddleB6Real]
        fun_prop
      exact hcont.intervalIntegrable _ _
    have hsumInt : IntervalIntegrable (fun x : ℝ => FS x + FE x) volume (-L) L :=
      hFSint.add hFEint
    have hInt :
        (∫ x in -L..L, FT x) ≤ (∫ x in -L..L, FS x) + (∫ x in -L..L, FE x) := by
      calc
        (∫ x in -L..L, FT x) ≤ ∫ x in -L..L, FS x + FE x :=
          intervalIntegral.integral_mono_on hle hFTint hsumInt hpoint
        _ = (∫ x in -L..L, FS x) + (∫ x in -L..L, FE x) := by
          rw [intervalIntegral.integral_add hFSint hFEint]
    have hdiv :
        (∫ x in -L..L, FT x) / blocks3SecondCorrScale r ≤
          ((∫ x in -L..L, FS x) + (∫ x in -L..L, FE x)) /
            blocks3SecondCorrScale r :=
      div_le_div_of_nonneg_right hInt hcorr.le
    calc
      T r = (∫ x in -L..L, FT x) / blocks3SecondCorrScale r := by rfl
      _ ≤ ((∫ x in -L..L, FS x) + (∫ x in -L..L, FE x)) /
            blocks3SecondCorrScale r := hdiv
      _ = S r + E r := by
        dsimp [S, E, FS, FE, L]
        ring

/-- The produced third-order H-admissible instance for blocks of size at most three. -/
def blocks3ThirdOrderHAdmissible :
    ThirdOrderHAdmissible blocks3HAdmissible blocks3SecondOrderHAdmissible where
  b5 := blocks3SaddleB5Real
  b6 := blocks3SaddleB6Real
  corrScale3 := blocks3ThirdCorrScale
  corrScale3_pos := by
    simpa [blocks3HAdmissible, blocks3ThirdCorrScale] using
      blocks3SecondCorrScale_pos_eventually
  corrScale3_tendsto_zero := by
    simpa [blocks3HAdmissible, blocks3ThirdCorrScale] using
      blocks3SecondCorrScale_tendsto_zero
  corrScale3_dominates_correction := by
    simpa [blocks3HAdmissible, blocks3SecondOrderHAdmissible, blocks3ThirdCorrScale]
      using blocks3_saddleThirdCorrectionScale_le_thirdCorrScale
  local_third_L1 := by
    simpa [blocks3HAdmissible, blocks3SecondOrderHAdmissible, blocks3ThirdCorrScale]
      using blocks3_local_third_L1
  tail_third_uniform := by
    simpa [blocks3HAdmissible, blocks3ThirdCorrScale] using blocks3_tail_second_uniform

/-- Abstract third-order saddle theorem specialized to the blocks-<=3 saddle. -/
theorem blocks3_coeff_thirdOrder_saddle_from_HAdmissible :
    (fun n : ℕ =>
      blocks3Series.coeff n / blocks3SecondOrderSaddleScale n -
        (1 + (blocks3SecondCorrectionAtSaddle n : ℂ) +
          (blocks3ThirdCorrectionAtSaddle n : ℂ)))
      =o[atTop]
    (fun n : ℕ => (blocks3ThirdCorrScale (blocks3SaddleRadius n) : ℂ)) := by
  have h :=
    coeff_thirdOrder_saddle
      blocks3HAdmissible blocks3SecondOrderHAdmissible blocks3ThirdOrderHAdmissible
      blocks3HAdmissibleSaddleSequence
  simpa [blocks3SecondOrderSaddleScale, blocks3SecondCorrectionAtSaddle,
    blocks3ThirdCorrectionAtSaddle, HAdmissible.B, blocks3HAdmissible,
    blocks3HAdmissibleSaddleSequence, blocks3SecondOrderHAdmissible,
    blocks3ThirdOrderHAdmissible, blocks3ThirdCorrScale] using h

/--
Third-order saddle ratio for set partitions with blocks of size at most three:
`B_3(n)/n!` divided by the saddle scale is
`1 + delta_1(r_n) + delta_2(r_n) + o(corrScale)`, with the exact
`delta_2 = saddleThirdCorrection ...`.
-/
theorem blocks3_number_over_factorial_thirdOrder_saddle :
    (fun n : ℕ => blocks3ThirdOrderNumberError n)
      =o[atTop]
    (fun n : ℕ => (blocks3ThirdCorrScale (blocks3SaddleRadius n) : ℂ)) := by
  simpa [blocks3ThirdOrderNumberError, blocks3SecondOrderSaddleScale,
    blocks3SecondCorrectionAtSaddle, blocks3ThirdCorrectionAtSaddle,
    PowerSeries.coeff_toFMLS, blocks3Carrier_coeff, blocks3CoeffR]
    using blocks3_coeff_thirdOrder_saddle_from_HAdmissible

end Blocks3HAdmissible
