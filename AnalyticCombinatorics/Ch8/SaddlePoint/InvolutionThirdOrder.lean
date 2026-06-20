import AnalyticCombinatorics.Ch8.SaddlePoint.ThirdOrderHAdmissible
import AnalyticCombinatorics.Ch8.SaddlePoint.InvolutionSecondOrder

/-!
# Third-order saddle data for involutions

This file instantiates the third-order Hayman wrapper for
`exp (z + z^2 / 2)`.  The fifth and sixth logarithmic saddle derivatives are
`b₅(r)=r+16r²` and `b₆(r)=r+32r²`.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval PowerSeries

set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

noncomputable section

namespace InvolutionHAdmissible

/-- Fifth logarithmic saddle derivative for involutions. -/
def involSaddleB5Real (r : ℝ) : ℝ :=
  r + 16 * r ^ 2

/-- Sixth logarithmic saddle derivative for involutions. -/
def involSaddleB6Real (r : ℝ) : ℝ :=
  r + 32 * r ^ 2

/--
Robust third-order scale used by the current `ThirdOrderHAdmissible` interface.
The abstract wrapper requires this scale to dominate the second-order absolute
coefficient scale, so for involutions the existing second-order scale is the
natural reusable choice.
-/
def involThirdCorrScale (r : ℝ) : ℝ :=
  involSecondCorrScale r

private lemma involSaddleBReal_pos_of_ge_one {r : ℝ} (hr : 1 ≤ r) :
    0 < involSaddleBReal r := by
  unfold involSaddleBReal
  nlinarith [hr, sq_nonneg r]

private lemma invol_sqrtB_ge_r {r : ℝ} (hr : 1 ≤ r) :
    r ≤ Real.sqrt (involSaddleBReal r) := by
  have hb_ge : r ^ 2 ≤ involSaddleBReal r := by
    unfold involSaddleBReal
    nlinarith [sq_nonneg r]
  exact Real.le_sqrt_of_sq_le hb_ge

private lemma invol_b_ge_r_sq {r : ℝ} (_hr : 1 ≤ r) :
    r ^ 2 ≤ involSaddleBReal r := by
  unfold involSaddleBReal
  nlinarith [sq_nonneg r]

private lemma invol_b_norm_eq_of_ge_one {r : ℝ} (hr : 1 ≤ r) :
    ‖(involSaddleBReal r : ℂ)‖ = involSaddleBReal r := by
  have hbpos : 0 < involSaddleBReal r := involSaddleBReal_pos_of_ge_one hr
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hbpos]

private lemma invol_sqrtB_norm_eq_of_ge_one {r : ℝ} (hr : 1 ≤ r) :
    ‖(Real.sqrt (involSaddleBReal r) : ℂ)‖ =
      Real.sqrt (involSaddleBReal r) := by
  have hbpos : 0 < involSaddleBReal r := involSaddleBReal_pos_of_ge_one hr
  have hsqrt_pos : 0 < Real.sqrt (involSaddleBReal r) := Real.sqrt_pos.mpr hbpos
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsqrt_pos]

private lemma invol_b3_nonneg_of_ge_one {r : ℝ} (hr : 1 ≤ r) :
    0 ≤ involSaddleB3Real r := by
  unfold involSaddleB3Real
  nlinarith [hr, sq_nonneg r]

private lemma invol_b4_nonneg_of_ge_one {r : ℝ} (hr : 1 ≤ r) :
    0 ≤ involSaddleB4Real r := by
  unfold involSaddleB4Real
  nlinarith [hr, sq_nonneg r]

private lemma invol_b5_nonneg_of_ge_one {r : ℝ} (hr : 1 ≤ r) :
    0 ≤ involSaddleB5Real r := by
  unfold involSaddleB5Real
  nlinarith [hr, sq_nonneg r]

private lemma invol_b6_nonneg_of_ge_one {r : ℝ} (hr : 1 ≤ r) :
    0 ≤ involSaddleB6Real r := by
  unfold involSaddleB6Real
  nlinarith [hr, sq_nonneg r]

private lemma invol_b3_le {r : ℝ} (hr : 1 ≤ r) :
    involSaddleB3Real r ≤ 5 * r ^ 2 := by
  unfold involSaddleB3Real
  nlinarith [hr]

private lemma invol_b4_le {r : ℝ} (hr : 1 ≤ r) :
    involSaddleB4Real r ≤ 9 * r ^ 2 := by
  unfold involSaddleB4Real
  nlinarith [hr]

private lemma invol_b5_le {r : ℝ} (hr : 1 ≤ r) :
    involSaddleB5Real r ≤ 17 * r ^ 2 := by
  unfold involSaddleB5Real
  nlinarith [hr]

private lemma invol_b6_le {r : ℝ} (hr : 1 ≤ r) :
    involSaddleB6Real r ≤ 33 * r ^ 2 := by
  unfold involSaddleB6Real
  nlinarith [hr]

private lemma invol_term_b6_le_rpow {r : ℝ} (hr : 1 ≤ r) :
    |involSaddleB6Real r| / (involSaddleBReal r) ^ 3 ≤
      100 * r ^ (-(2 : ℝ)) := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  rw [Real.rpow_neg hrpos.le]
  rw [show r ^ (2 : ℝ) = r ^ 2 by exact Real.rpow_natCast r 2]
  unfold involSaddleB6Real involSaddleBReal
  have hnum_nonneg : 0 ≤ r + 32 * r ^ 2 := by positivity
  rw [abs_of_nonneg hnum_nonneg]
  field_simp [hrpos.ne']
  ring_nf
  have hdiff : 0 ≤ 99 * r ^ 2 + 568 * r ^ 3 + 1200 * r ^ 4 + 800 * r ^ 5 := by
    positivity
  nlinarith [hdiff]

private lemma invol_term_b3b5_le_rpow {r : ℝ} (hr : 1 ≤ r) :
    |involSaddleB3Real r * involSaddleB5Real r| / (involSaddleBReal r) ^ 4 ≤
      1000 * r ^ (-(2 : ℝ)) := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  rw [Real.rpow_neg hrpos.le]
  rw [show r ^ (2 : ℝ) = r ^ 2 by exact Real.rpow_natCast r 2]
  unfold involSaddleB3Real involSaddleB5Real involSaddleBReal
  have hnum_nonneg : 0 ≤ (r + 4 * r ^ 2) * (r + 16 * r ^ 2) := by positivity
  rw [abs_of_nonneg hnum_nonneg]
  field_simp [hrpos.ne']
  ring_nf
  nlinarith [hr, sq_nonneg r, show 0 ≤ r ^ 3 by positivity, show 0 ≤ r ^ 4 by positivity,
    show 0 ≤ r ^ 5 by positivity, show 0 ≤ r ^ 6 by positivity,
    show 0 ≤ r ^ 7 by positivity, show 0 ≤ r ^ 8 by positivity]

private lemma invol_term_b4sq_le_rpow {r : ℝ} (hr : 1 ≤ r) :
    (involSaddleB4Real r) ^ 2 / (involSaddleBReal r) ^ 4 ≤
      1000 * r ^ (-(2 : ℝ)) := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  rw [Real.rpow_neg hrpos.le]
  rw [show r ^ (2 : ℝ) = r ^ 2 by exact Real.rpow_natCast r 2]
  unfold involSaddleB4Real involSaddleBReal
  field_simp [hrpos.ne']
  ring_nf
  nlinarith [hr, sq_nonneg r, show 0 ≤ r ^ 3 by positivity, show 0 ≤ r ^ 4 by positivity,
    show 0 ≤ r ^ 5 by positivity, show 0 ≤ r ^ 6 by positivity,
    show 0 ≤ r ^ 7 by positivity, show 0 ≤ r ^ 8 by positivity]

private lemma invol_term_b3sqb4_le_rpow {r : ℝ} (hr : 1 ≤ r) :
    (involSaddleB3Real r) ^ 2 * |involSaddleB4Real r| /
        (involSaddleBReal r) ^ 5 ≤
      1000 * r ^ (-(2 : ℝ)) := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  rw [Real.rpow_neg hrpos.le]
  rw [show r ^ (2 : ℝ) = r ^ 2 by exact Real.rpow_natCast r 2]
  unfold involSaddleB3Real involSaddleB4Real involSaddleBReal
  have hb4_nonneg : 0 ≤ r + 8 * r ^ 2 := by positivity
  rw [abs_of_nonneg hb4_nonneg]
  field_simp [hrpos.ne']
  ring_nf
  nlinarith [hr, sq_nonneg r, show 0 ≤ r ^ 3 by positivity, show 0 ≤ r ^ 4 by positivity,
    show 0 ≤ r ^ 5 by positivity, show 0 ≤ r ^ 6 by positivity,
    show 0 ≤ r ^ 7 by positivity, show 0 ≤ r ^ 8 by positivity,
    show 0 ≤ r ^ 9 by positivity, show 0 ≤ r ^ 10 by positivity]

private lemma invol_term_b3four_le_rpow {r : ℝ} (hr : 1 ≤ r) :
    (involSaddleB3Real r) ^ 4 / (involSaddleBReal r) ^ 6 ≤
      1000 * r ^ (-(2 : ℝ)) := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  rw [Real.rpow_neg hrpos.le]
  rw [show r ^ (2 : ℝ) = r ^ 2 by exact Real.rpow_natCast r 2]
  unfold involSaddleB3Real involSaddleBReal
  field_simp [hrpos.ne']
  ring_nf
  nlinarith [hr, sq_nonneg r, show 0 ≤ r ^ 3 by positivity, show 0 ≤ r ^ 4 by positivity,
    show 0 ≤ r ^ 5 by positivity, show 0 ≤ r ^ 6 by positivity,
    show 0 ≤ r ^ 7 by positivity, show 0 ≤ r ^ 8 by positivity,
    show 0 ≤ r ^ 9 by positivity, show 0 ≤ r ^ 10 by positivity,
    show 0 ≤ r ^ 11 by positivity, show 0 ≤ r ^ 12 by positivity]

lemma invol_saddleThirdCorrectionScale_le_second :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ᶠ r : ℝ in atTop,
        saddleThirdCorrectionScale involSaddleBReal involSaddleB3Real involSaddleB4Real
          involSaddleB5Real involSaddleB6Real r ≤ K * involThirdCorrScale r := by
  refine ⟨200000, by norm_num, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ), involSecondCorrScale_lower_eventually] with
    r hr hsecondLower
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hαpos : 0 < (16 / 27 : ℝ) * r ^ (-(2 : ℝ)) := by positivity
  have hsecond_pos : 0 < involSecondCorrScale r := lt_of_lt_of_le hαpos hsecondLower
  have hbpos : 0 < involSaddleBReal r := involSaddleBReal_pos_of_ge_one hr
  have hdiv_nonneg₁ :
      0 ≤ |involSaddleB6Real r| / (involSaddleBReal r) ^ 3 := by positivity
  have hdiv_nonneg₂ :
      0 ≤ |involSaddleB3Real r * involSaddleB5Real r| / (involSaddleBReal r) ^ 4 := by
    positivity
  have hdiv_nonneg₃ :
      0 ≤ (involSaddleB4Real r) ^ 2 / (involSaddleBReal r) ^ 4 := by positivity
  have hdiv_nonneg₄ :
      0 ≤ (involSaddleB3Real r) ^ 2 * |involSaddleB4Real r| /
          (involSaddleBReal r) ^ 5 := by
    positivity
  have hdiv_nonneg₅ :
      0 ≤ (involSaddleB3Real r) ^ 4 / (involSaddleBReal r) ^ 6 := by positivity
  have hterm₁ := invol_term_b6_le_rpow hr
  have hterm₂ := invol_term_b3b5_le_rpow hr
  have hterm₃ := invol_term_b4sq_le_rpow hr
  have hterm₄ := invol_term_b3sqb4_le_rpow hr
  have hterm₅ := invol_term_b3four_le_rpow hr
  have hthird :
      |involSaddleB6Real r| / (involSaddleBReal r) ^ 3
        + |involSaddleB3Real r * involSaddleB5Real r| / (involSaddleBReal r) ^ 4
        + (involSaddleB4Real r) ^ 2 / (involSaddleBReal r) ^ 4
        + (involSaddleB3Real r) ^ 2 * |involSaddleB4Real r| /
            (involSaddleBReal r) ^ 5
        + (involSaddleB3Real r) ^ 4 / (involSaddleBReal r) ^ 6
        ≤ 4100 * r ^ (-(2 : ℝ)) := by
    nlinarith
  have hthird_second :
      |involSaddleB6Real r| / (involSaddleBReal r) ^ 3
        + |involSaddleB3Real r * involSaddleB5Real r| / (involSaddleBReal r) ^ 4
        + (involSaddleB4Real r) ^ 2 / (involSaddleBReal r) ^ 4
        + (involSaddleB3Real r) ^ 2 * |involSaddleB4Real r| /
            (involSaddleBReal r) ^ 5
        + (involSaddleB3Real r) ^ 4 / (involSaddleBReal r) ^ 6
        ≤ 100000 * involSecondCorrScale r := by
    calc
      |involSaddleB6Real r| / (involSaddleBReal r) ^ 3
        + |involSaddleB3Real r * involSaddleB5Real r| / (involSaddleBReal r) ^ 4
        + (involSaddleB4Real r) ^ 2 / (involSaddleBReal r) ^ 4
        + (involSaddleB3Real r) ^ 2 * |involSaddleB4Real r| /
            (involSaddleBReal r) ^ 5
        + (involSaddleB3Real r) ^ 4 / (involSaddleBReal r) ^ 6
          ≤ 4100 * r ^ (-(2 : ℝ)) := hthird
      _ ≤ 100000 * involSecondCorrScale r := by
        nlinarith
  have htarget :
      saddleCorrectionScale involSaddleBReal involSaddleB3Real involSaddleB4Real r
        + |involSaddleB6Real r| / (involSaddleBReal r) ^ 3
        + |involSaddleB3Real r * involSaddleB5Real r| / (involSaddleBReal r) ^ 4
        + (involSaddleB4Real r) ^ 2 / (involSaddleBReal r) ^ 4
        + (involSaddleB3Real r) ^ 2 * |involSaddleB4Real r| /
            (involSaddleBReal r) ^ 5
        + (involSaddleB3Real r) ^ 4 / (involSaddleBReal r) ^ 6
      ≤ 200000 * involThirdCorrScale r := by
    change involSecondCorrScale r
        + |involSaddleB6Real r| / (involSaddleBReal r) ^ 3
        + |involSaddleB3Real r * involSaddleB5Real r| / (involSaddleBReal r) ^ 4
        + (involSaddleB4Real r) ^ 2 / (involSaddleBReal r) ^ 4
        + (involSaddleB3Real r) ^ 2 * |involSaddleB4Real r| /
            (involSaddleBReal r) ^ 5
        + (involSaddleB3Real r) ^ 4 / (involSaddleBReal r) ^ 6
      ≤ 200000 * involThirdCorrScale r
    unfold involThirdCorrScale
    nlinarith [hthird_second, hsecond_pos.le]
  simpa [saddleThirdCorrectionScale, involThirdCorrScale] using htarget

private def involThirdGaussianDom (x : ℝ) : ℝ :=
  Real.exp (-(x ^ 2) / 2) *
    (|x| ^ 5 + |x| ^ 6 + |x| ^ 7 + |x| ^ 8 +
      |x| ^ 9 + |x| ^ 10 + |x| ^ 12)

private lemma involThirdGaussianDom_nonneg (x : ℝ) : 0 ≤ involThirdGaussianDom x := by
  unfold involThirdGaussianDom
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

private lemma involThirdGaussianDom_integrable : Integrable involThirdGaussianDom := by
  unfold involThirdGaussianDom
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

private lemma involThirdGaussianDom_integral_nonneg :
    0 ≤ ∫ x : ℝ, involThirdGaussianDom x := by
  exact integral_nonneg (fun x => involThirdGaussianDom_nonneg x)

private lemma involThirdGaussianDom_continuous : Continuous involThirdGaussianDom := by
  unfold involThirdGaussianDom
  fun_prop

private lemma involThirdGaussianDom_window_le_integral {L : ℝ} (hL : 0 ≤ L) :
    (∫ x in -L..L, involThirdGaussianDom x) ≤ ∫ x : ℝ, involThirdGaussianDom x := by
  have hle : -L ≤ L := by linarith
  rw [intervalIntegral.integral_of_le hle]
  exact setIntegral_le_integral involThirdGaussianDom_integrable
    (Eventually.of_forall involThirdGaussianDom_nonneg)

private lemma invol_third_extra5_norm_le {r x : ℝ} (hr : 1 ≤ r) :
    ‖Complex.I * ((involSaddleB5Real r : ℂ) /
      (120 * (Real.sqrt (involSaddleBReal r) : ℂ) ^ 5)) * (x : ℂ) ^ 5‖ ≤
        10 * |x| ^ 5 / r ^ 3 := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hbpos : 0 < involSaddleBReal r := involSaddleBReal_pos_of_ge_one hr
  have hsqrt_pos : 0 < Real.sqrt (involSaddleBReal r) := Real.sqrt_pos.mpr hbpos
  have hsqrt_ge : r ≤ Real.sqrt (involSaddleBReal r) := invol_sqrtB_ge_r hr
  have hsqrt5_ge : r ^ 5 ≤ (Real.sqrt (involSaddleBReal r)) ^ 5 :=
    pow_le_pow_left₀ hrpos.le hsqrt_ge 5
  have hcoef :
      ‖(involSaddleB5Real r : ℂ) /
          (120 * (Real.sqrt (involSaddleBReal r) : ℂ) ^ 5)‖ ≤ 1 / r ^ 3 := by
    calc
      ‖(involSaddleB5Real r : ℂ) /
          (120 * (Real.sqrt (involSaddleBReal r) : ℂ) ^ 5)‖
          = involSaddleB5Real r /
              (120 * |Real.sqrt (involSaddleBReal r)| ^ 5) := by
            rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (invol_b5_nonneg_of_ge_one hr)]
            simp [norm_pow, Complex.norm_real, Real.norm_eq_abs]
      _ = involSaddleB5Real r /
              (120 * (Real.sqrt (involSaddleBReal r)) ^ 5) := by
            rw [abs_of_pos hsqrt_pos]
      _ ≤ (17 * r ^ 2) / (120 * r ^ 5) := by
            exact div_le_div₀ (by positivity) (invol_b5_le hr) (by positivity)
              (by nlinarith [hsqrt5_ge])
      _ ≤ 1 / r ^ 3 := by
            field_simp [hrpos.ne']
            nlinarith
  calc
    ‖Complex.I * ((involSaddleB5Real r : ℂ) /
      (120 * (Real.sqrt (involSaddleBReal r) : ℂ) ^ 5)) * (x : ℂ) ^ 5‖
        = ‖(involSaddleB5Real r : ℂ) /
            (120 * (Real.sqrt (involSaddleBReal r) : ℂ) ^ 5)‖ * |x| ^ 5 := by
          rw [norm_mul, norm_mul, norm_I, one_mul, norm_pow, Complex.norm_real,
            Real.norm_eq_abs]
    _ ≤ (1 / r ^ 3) * |x| ^ 5 :=
          mul_le_mul_of_nonneg_right hcoef (pow_nonneg (abs_nonneg x) 5)
    _ ≤ 10 * |x| ^ 5 / r ^ 3 := by
          have hr3pos : 0 < r ^ 3 := by positivity
          field_simp [hr3pos.ne']
          nlinarith [pow_nonneg (abs_nonneg x) 5]

private lemma invol_third_extra6_norm_le {r x : ℝ} (hr : 1 ≤ r) :
    ‖((involSaddleB6Real r : ℂ) / (720 * (involSaddleBReal r : ℂ) ^ 3)) *
        (x : ℂ) ^ 6‖ ≤ 10 * |x| ^ 6 / r ^ 3 := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hb_ge : r ^ 2 ≤ involSaddleBReal r := invol_b_ge_r_sq hr
  have hb3_ge : r ^ 6 ≤ (involSaddleBReal r) ^ 3 := by
    calc
      r ^ 6 = (r ^ 2) ^ 3 := by ring
      _ ≤ (involSaddleBReal r) ^ 3 := pow_le_pow_left₀ (sq_nonneg r) hb_ge 3
  have hcoef :
      ‖(involSaddleB6Real r : ℂ) / (720 * (involSaddleBReal r : ℂ) ^ 3)‖
        ≤ 1 / r ^ 3 := by
    calc
      ‖(involSaddleB6Real r : ℂ) / (720 * (involSaddleBReal r : ℂ) ^ 3)‖
          = involSaddleB6Real r / (720 * (involSaddleBReal r) ^ 3) := by
            rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (invol_b6_nonneg_of_ge_one hr)]
            simp only [norm_mul, Complex.norm_ofNat, norm_pow]
            rw [invol_b_norm_eq_of_ge_one hr]
      _ ≤ (33 * r ^ 2) / (720 * r ^ 6) := by
            exact div_le_div₀ (by positivity) (invol_b6_le hr) (by positivity)
              (by nlinarith [hb3_ge])
      _ ≤ 1 / r ^ 3 := by
            field_simp [hrpos.ne']
            nlinarith [hr]
  calc
    ‖((involSaddleB6Real r : ℂ) / (720 * (involSaddleBReal r : ℂ) ^ 3)) *
        (x : ℂ) ^ 6‖
        = ‖(involSaddleB6Real r : ℂ) /
            (720 * (involSaddleBReal r : ℂ) ^ 3)‖ * |x| ^ 6 := by
          rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (1 / r ^ 3) * |x| ^ 6 :=
          mul_le_mul_of_nonneg_right hcoef (pow_nonneg (abs_nonneg x) 6)
    _ ≤ 10 * |x| ^ 6 / r ^ 3 := by
          have hr3pos : 0 < r ^ 3 := by positivity
          field_simp [hr3pos.ne']
          nlinarith [pow_nonneg (abs_nonneg x) 6]

private lemma invol_third_extra7_norm_le {r x : ℝ} (hr : 1 ≤ r) :
    ‖Complex.I * (((involSaddleB3Real r * involSaddleB4Real r : ℝ) : ℂ) /
      (144 * (Real.sqrt (involSaddleBReal r) : ℂ) ^ 3 *
        (involSaddleBReal r : ℂ) ^ 2)) * (x : ℂ) ^ 7‖ ≤
        10 * |x| ^ 7 / r ^ 3 := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hsqrt_ge : r ≤ Real.sqrt (involSaddleBReal r) := invol_sqrtB_ge_r hr
  have hb_ge : r ^ 2 ≤ involSaddleBReal r := invol_b_ge_r_sq hr
  have hsqrt3_ge : r ^ 3 ≤ (Real.sqrt (involSaddleBReal r)) ^ 3 :=
    pow_le_pow_left₀ hrpos.le hsqrt_ge 3
  have hb2_ge : r ^ 4 ≤ (involSaddleBReal r) ^ 2 := by
    calc
      r ^ 4 = (r ^ 2) ^ 2 := by ring
      _ ≤ (involSaddleBReal r) ^ 2 := pow_le_pow_left₀ (sq_nonneg r) hb_ge 2
  have hden_ge :
      r ^ 7 ≤ (Real.sqrt (involSaddleBReal r)) ^ 3 * (involSaddleBReal r) ^ 2 := by
    calc
      r ^ 7 = r ^ 3 * r ^ 4 := by ring
      _ ≤ (Real.sqrt (involSaddleBReal r)) ^ 3 * (involSaddleBReal r) ^ 2 :=
        mul_le_mul hsqrt3_ge hb2_ge (by positivity) (by positivity)
  have hnum_nonneg : 0 ≤ involSaddleB3Real r * involSaddleB4Real r :=
    mul_nonneg (invol_b3_nonneg_of_ge_one hr) (invol_b4_nonneg_of_ge_one hr)
  have hnum_le : involSaddleB3Real r * involSaddleB4Real r ≤ 45 * r ^ 4 := by
    calc
      involSaddleB3Real r * involSaddleB4Real r
          ≤ (5 * r ^ 2) * (9 * r ^ 2) :=
            mul_le_mul (invol_b3_le hr) (invol_b4_le hr)
              (invol_b4_nonneg_of_ge_one hr) (by positivity)
      _ = 45 * r ^ 4 := by ring
  have hcoef :
      ‖(((involSaddleB3Real r * involSaddleB4Real r : ℝ) : ℂ) /
        (144 * (Real.sqrt (involSaddleBReal r) : ℂ) ^ 3 *
          (involSaddleBReal r : ℂ) ^ 2))‖ ≤ 1 / r ^ 3 := by
    calc
      ‖(((involSaddleB3Real r * involSaddleB4Real r : ℝ) : ℂ) /
        (144 * (Real.sqrt (involSaddleBReal r) : ℂ) ^ 3 *
          (involSaddleBReal r : ℂ) ^ 2))‖
          =
            (involSaddleB3Real r * involSaddleB4Real r) /
              (144 * (Real.sqrt (involSaddleBReal r)) ^ 3 *
                (involSaddleBReal r) ^ 2) := by
            rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg hnum_nonneg]
            simp only [norm_mul, Complex.norm_ofNat, norm_pow]
            rw [invol_sqrtB_norm_eq_of_ge_one hr, invol_b_norm_eq_of_ge_one hr]
      _ ≤ (45 * r ^ 4) / (144 * r ^ 7) := by
            exact div_le_div₀ (by positivity) hnum_le (by positivity)
              (by nlinarith [hden_ge])
      _ ≤ 1 / r ^ 3 := by
            field_simp [hrpos.ne']
            nlinarith [hr]
  calc
    ‖Complex.I * (((involSaddleB3Real r * involSaddleB4Real r : ℝ) : ℂ) /
      (144 * (Real.sqrt (involSaddleBReal r) : ℂ) ^ 3 *
        (involSaddleBReal r : ℂ) ^ 2)) * (x : ℂ) ^ 7‖
        = ‖(((involSaddleB3Real r * involSaddleB4Real r : ℝ) : ℂ) /
            (144 * (Real.sqrt (involSaddleBReal r) : ℂ) ^ 3 *
              (involSaddleBReal r : ℂ) ^ 2))‖ * |x| ^ 7 := by
          rw [norm_mul, norm_mul, norm_I, one_mul, norm_pow, Complex.norm_real,
            Real.norm_eq_abs]
    _ ≤ (1 / r ^ 3) * |x| ^ 7 :=
          mul_le_mul_of_nonneg_right hcoef (pow_nonneg (abs_nonneg x) 7)
    _ ≤ 10 * |x| ^ 7 / r ^ 3 := by
          have hr3pos : 0 < r ^ 3 := by positivity
          field_simp [hr3pos.ne']
          nlinarith [pow_nonneg (abs_nonneg x) 7]

private lemma invol_third_extra8a_norm_le {r x : ℝ} (hr : 1 ≤ r) :
    ‖(((involSaddleB3Real r * involSaddleB5Real r : ℝ) : ℂ) /
      (720 * (involSaddleBReal r : ℂ) ^ 4)) * (x : ℂ) ^ 8‖ ≤
        10 * |x| ^ 8 / r ^ 3 := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hb_ge : r ^ 2 ≤ involSaddleBReal r := invol_b_ge_r_sq hr
  have hb4_ge : r ^ 8 ≤ (involSaddleBReal r) ^ 4 := by
    calc
      r ^ 8 = (r ^ 2) ^ 4 := by ring
      _ ≤ (involSaddleBReal r) ^ 4 := pow_le_pow_left₀ (sq_nonneg r) hb_ge 4
  have hnum_nonneg : 0 ≤ involSaddleB3Real r * involSaddleB5Real r :=
    mul_nonneg (invol_b3_nonneg_of_ge_one hr) (invol_b5_nonneg_of_ge_one hr)
  have hnum_le : involSaddleB3Real r * involSaddleB5Real r ≤ 85 * r ^ 4 := by
    calc
      involSaddleB3Real r * involSaddleB5Real r
          ≤ (5 * r ^ 2) * (17 * r ^ 2) :=
            mul_le_mul (invol_b3_le hr) (invol_b5_le hr)
              (invol_b5_nonneg_of_ge_one hr) (by positivity)
      _ = 85 * r ^ 4 := by ring
  have hcoef :
      ‖(((involSaddleB3Real r * involSaddleB5Real r : ℝ) : ℂ) /
        (720 * (involSaddleBReal r : ℂ) ^ 4))‖ ≤ 1 / r ^ 3 := by
    calc
      ‖(((involSaddleB3Real r * involSaddleB5Real r : ℝ) : ℂ) /
        (720 * (involSaddleBReal r : ℂ) ^ 4))‖
          = (involSaddleB3Real r * involSaddleB5Real r) /
              (720 * (involSaddleBReal r) ^ 4) := by
            rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg hnum_nonneg]
            simp only [norm_mul, Complex.norm_ofNat, norm_pow]
            rw [invol_b_norm_eq_of_ge_one hr]
      _ ≤ (85 * r ^ 4) / (720 * r ^ 8) := by
            exact div_le_div₀ (by positivity) hnum_le (by positivity)
              (by nlinarith [hb4_ge])
      _ ≤ 1 / r ^ 3 := by
            field_simp [hrpos.ne']
            nlinarith [hr]
  calc
    ‖(((involSaddleB3Real r * involSaddleB5Real r : ℝ) : ℂ) /
      (720 * (involSaddleBReal r : ℂ) ^ 4)) * (x : ℂ) ^ 8‖
        = ‖(((involSaddleB3Real r * involSaddleB5Real r : ℝ) : ℂ) /
            (720 * (involSaddleBReal r : ℂ) ^ 4))‖ * |x| ^ 8 := by
          rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (1 / r ^ 3) * |x| ^ 8 :=
          mul_le_mul_of_nonneg_right hcoef (pow_nonneg (abs_nonneg x) 8)
    _ ≤ 10 * |x| ^ 8 / r ^ 3 := by
          have hr3pos : 0 < r ^ 3 := by positivity
          field_simp [hr3pos.ne']
          nlinarith [pow_nonneg (abs_nonneg x) 8]

private lemma invol_third_extra8b_norm_le {r x : ℝ} (hr : 1 ≤ r) :
    ‖((((involSaddleB4Real r) ^ 2 : ℝ) : ℂ) /
      (1152 * (involSaddleBReal r : ℂ) ^ 4)) * (x : ℂ) ^ 8‖ ≤
        10 * |x| ^ 8 / r ^ 3 := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hb_ge : r ^ 2 ≤ involSaddleBReal r := invol_b_ge_r_sq hr
  have hb4_ge : r ^ 8 ≤ (involSaddleBReal r) ^ 4 := by
    calc
      r ^ 8 = (r ^ 2) ^ 4 := by ring
      _ ≤ (involSaddleBReal r) ^ 4 := pow_le_pow_left₀ (sq_nonneg r) hb_ge 4
  have hnum_le : (involSaddleB4Real r) ^ 2 ≤ 81 * r ^ 4 := by
    calc
      (involSaddleB4Real r) ^ 2 ≤ (9 * r ^ 2) ^ 2 :=
        pow_le_pow_left₀ (invol_b4_nonneg_of_ge_one hr) (invol_b4_le hr) 2
      _ = 81 * r ^ 4 := by ring
  have hcoef :
      ‖((((involSaddleB4Real r) ^ 2 : ℝ) : ℂ) /
        (1152 * (involSaddleBReal r : ℂ) ^ 4))‖ ≤ 1 / r ^ 3 := by
    calc
      ‖((((involSaddleB4Real r) ^ 2 : ℝ) : ℂ) /
        (1152 * (involSaddleBReal r : ℂ) ^ 4))‖
          = (involSaddleB4Real r) ^ 2 / (1152 * (involSaddleBReal r) ^ 4) := by
            rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (sq_nonneg _)]
            simp only [norm_mul, Complex.norm_ofNat, norm_pow]
            rw [invol_b_norm_eq_of_ge_one hr]
      _ ≤ (81 * r ^ 4) / (1152 * r ^ 8) := by
            exact div_le_div₀ (by positivity) hnum_le (by positivity)
              (by nlinarith [hb4_ge])
      _ ≤ 1 / r ^ 3 := by
            field_simp [hrpos.ne']
            nlinarith [hr]
  calc
    ‖((((involSaddleB4Real r) ^ 2 : ℝ) : ℂ) /
      (1152 * (involSaddleBReal r : ℂ) ^ 4)) * (x : ℂ) ^ 8‖
        = ‖((((involSaddleB4Real r) ^ 2 : ℝ) : ℂ) /
            (1152 * (involSaddleBReal r : ℂ) ^ 4))‖ * |x| ^ 8 := by
          rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (1 / r ^ 3) * |x| ^ 8 :=
          mul_le_mul_of_nonneg_right hcoef (pow_nonneg (abs_nonneg x) 8)
    _ ≤ 10 * |x| ^ 8 / r ^ 3 := by
          have hr3pos : 0 < r ^ 3 := by positivity
          field_simp [hr3pos.ne']
          nlinarith [pow_nonneg (abs_nonneg x) 8]

private lemma invol_third_extra9_norm_le {r x : ℝ} (hr : 1 ≤ r) :
    ‖Complex.I * ((((involSaddleB3Real r) ^ 3 : ℝ) : ℂ) /
      (1296 * (Real.sqrt (involSaddleBReal r) : ℂ) ^ 9)) * (x : ℂ) ^ 9‖ ≤
        10 * |x| ^ 9 / r ^ 3 := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hsqrt_ge : r ≤ Real.sqrt (involSaddleBReal r) := invol_sqrtB_ge_r hr
  have hsqrt9_ge : r ^ 9 ≤ (Real.sqrt (involSaddleBReal r)) ^ 9 :=
    pow_le_pow_left₀ hrpos.le hsqrt_ge 9
  have hnum_le : (involSaddleB3Real r) ^ 3 ≤ 125 * r ^ 6 := by
    calc
      (involSaddleB3Real r) ^ 3 ≤ (5 * r ^ 2) ^ 3 :=
        pow_le_pow_left₀ (invol_b3_nonneg_of_ge_one hr) (invol_b3_le hr) 3
      _ = 125 * r ^ 6 := by ring
  have hcoef :
      ‖((((involSaddleB3Real r) ^ 3 : ℝ) : ℂ) /
        (1296 * (Real.sqrt (involSaddleBReal r) : ℂ) ^ 9))‖ ≤ 1 / r ^ 3 := by
    calc
      ‖((((involSaddleB3Real r) ^ 3 : ℝ) : ℂ) /
        (1296 * (Real.sqrt (involSaddleBReal r) : ℂ) ^ 9))‖
          = (involSaddleB3Real r) ^ 3 /
              (1296 * (Real.sqrt (involSaddleBReal r)) ^ 9) := by
            rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (pow_nonneg (invol_b3_nonneg_of_ge_one hr) 3)]
            simp only [norm_mul, Complex.norm_ofNat, norm_pow]
            rw [invol_sqrtB_norm_eq_of_ge_one hr]
      _ ≤ (125 * r ^ 6) / (1296 * r ^ 9) := by
            exact div_le_div₀ (by positivity) hnum_le (by positivity)
              (by nlinarith [hsqrt9_ge])
      _ ≤ 1 / r ^ 3 := by
            field_simp [hrpos.ne']
            nlinarith [hr]
  calc
    ‖Complex.I * ((((involSaddleB3Real r) ^ 3 : ℝ) : ℂ) /
      (1296 * (Real.sqrt (involSaddleBReal r) : ℂ) ^ 9)) * (x : ℂ) ^ 9‖
        = ‖((((involSaddleB3Real r) ^ 3 : ℝ) : ℂ) /
            (1296 * (Real.sqrt (involSaddleBReal r) : ℂ) ^ 9))‖ * |x| ^ 9 := by
          rw [norm_mul, norm_mul, norm_I, one_mul, norm_pow, Complex.norm_real,
            Real.norm_eq_abs]
    _ ≤ (1 / r ^ 3) * |x| ^ 9 :=
          mul_le_mul_of_nonneg_right hcoef (pow_nonneg (abs_nonneg x) 9)
    _ ≤ 10 * |x| ^ 9 / r ^ 3 := by
          have hr3pos : 0 < r ^ 3 := by positivity
          field_simp [hr3pos.ne']
          nlinarith [pow_nonneg (abs_nonneg x) 9]

private lemma invol_third_extra10_norm_le {r x : ℝ} (hr : 1 ≤ r) :
    ‖(((((involSaddleB3Real r) ^ 2 * involSaddleB4Real r : ℝ) : ℂ) /
      (1728 * (involSaddleBReal r : ℂ) ^ 5)) * (x : ℂ) ^ 10)‖ ≤
        10 * |x| ^ 10 / r ^ 3 := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hb_ge : r ^ 2 ≤ involSaddleBReal r := invol_b_ge_r_sq hr
  have hb5_ge : r ^ 10 ≤ (involSaddleBReal r) ^ 5 := by
    calc
      r ^ 10 = (r ^ 2) ^ 5 := by ring
      _ ≤ (involSaddleBReal r) ^ 5 := pow_le_pow_left₀ (sq_nonneg r) hb_ge 5
  have hnum_nonneg : 0 ≤ (involSaddleB3Real r) ^ 2 * involSaddleB4Real r :=
    mul_nonneg (sq_nonneg _) (invol_b4_nonneg_of_ge_one hr)
  have hnum_le : (involSaddleB3Real r) ^ 2 * involSaddleB4Real r ≤ 225 * r ^ 6 := by
    have hb3sq : (involSaddleB3Real r) ^ 2 ≤ (5 * r ^ 2) ^ 2 :=
      pow_le_pow_left₀ (invol_b3_nonneg_of_ge_one hr) (invol_b3_le hr) 2
    calc
      (involSaddleB3Real r) ^ 2 * involSaddleB4Real r
          ≤ (5 * r ^ 2) ^ 2 * (9 * r ^ 2) :=
            mul_le_mul hb3sq (invol_b4_le hr)
              (invol_b4_nonneg_of_ge_one hr) (by positivity)
      _ = 225 * r ^ 6 := by ring
  have hcoef :
      ‖(((((involSaddleB3Real r) ^ 2 * involSaddleB4Real r : ℝ) : ℂ) /
        (1728 * (involSaddleBReal r : ℂ) ^ 5)))‖ ≤ 1 / r ^ 3 := by
    calc
      ‖(((((involSaddleB3Real r) ^ 2 * involSaddleB4Real r : ℝ) : ℂ) /
        (1728 * (involSaddleBReal r : ℂ) ^ 5)))‖
          = ((involSaddleB3Real r) ^ 2 * involSaddleB4Real r) /
              (1728 * (involSaddleBReal r) ^ 5) := by
            rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg hnum_nonneg]
            simp only [norm_mul, Complex.norm_ofNat, norm_pow]
            rw [invol_b_norm_eq_of_ge_one hr]
      _ ≤ (225 * r ^ 6) / (1728 * r ^ 10) := by
            exact div_le_div₀ (by positivity) hnum_le (by positivity)
              (by nlinarith [hb5_ge])
      _ ≤ 1 / r ^ 3 := by
            field_simp [hrpos.ne']
            nlinarith [hr]
  calc
    ‖(((((involSaddleB3Real r) ^ 2 * involSaddleB4Real r : ℝ) : ℂ) /
      (1728 * (involSaddleBReal r : ℂ) ^ 5)) * (x : ℂ) ^ 10)‖
        = ‖(((((involSaddleB3Real r) ^ 2 * involSaddleB4Real r : ℝ) : ℂ) /
            (1728 * (involSaddleBReal r : ℂ) ^ 5)))‖ * |x| ^ 10 := by
          rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (1 / r ^ 3) * |x| ^ 10 :=
          mul_le_mul_of_nonneg_right hcoef (pow_nonneg (abs_nonneg x) 10)
    _ ≤ 10 * |x| ^ 10 / r ^ 3 := by
          have hr3pos : 0 < r ^ 3 := by positivity
          field_simp [hr3pos.ne']
          nlinarith [pow_nonneg (abs_nonneg x) 10]

private lemma invol_third_extra12_norm_le {r x : ℝ} (hr : 1 ≤ r) :
    ‖((((involSaddleB3Real r) ^ 4 : ℝ) : ℂ) /
      (31104 * (involSaddleBReal r : ℂ) ^ 6)) * (x : ℂ) ^ 12‖ ≤
        10 * |x| ^ 12 / r ^ 3 := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hb_ge : r ^ 2 ≤ involSaddleBReal r := invol_b_ge_r_sq hr
  have hb6_ge : r ^ 12 ≤ (involSaddleBReal r) ^ 6 := by
    calc
      r ^ 12 = (r ^ 2) ^ 6 := by ring
      _ ≤ (involSaddleBReal r) ^ 6 := pow_le_pow_left₀ (sq_nonneg r) hb_ge 6
  have hnum_le : (involSaddleB3Real r) ^ 4 ≤ 625 * r ^ 8 := by
    calc
      (involSaddleB3Real r) ^ 4 ≤ (5 * r ^ 2) ^ 4 :=
        pow_le_pow_left₀ (invol_b3_nonneg_of_ge_one hr) (invol_b3_le hr) 4
      _ = 625 * r ^ 8 := by ring
  have hcoef :
      ‖((((involSaddleB3Real r) ^ 4 : ℝ) : ℂ) /
        (31104 * (involSaddleBReal r : ℂ) ^ 6))‖ ≤ 1 / r ^ 3 := by
    calc
      ‖((((involSaddleB3Real r) ^ 4 : ℝ) : ℂ) /
        (31104 * (involSaddleBReal r : ℂ) ^ 6))‖
          = (involSaddleB3Real r) ^ 4 / (31104 * (involSaddleBReal r) ^ 6) := by
            rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (pow_nonneg (invol_b3_nonneg_of_ge_one hr) 4)]
            simp only [norm_mul, Complex.norm_ofNat, norm_pow]
            rw [invol_b_norm_eq_of_ge_one hr]
      _ ≤ (625 * r ^ 8) / (31104 * r ^ 12) := by
            exact div_le_div₀ (by positivity) hnum_le (by positivity)
              (by nlinarith [hb6_ge])
      _ ≤ 1 / r ^ 3 := by
            field_simp [hrpos.ne']
            nlinarith [hr]
  calc
    ‖((((involSaddleB3Real r) ^ 4 : ℝ) : ℂ) /
      (31104 * (involSaddleBReal r : ℂ) ^ 6)) * (x : ℂ) ^ 12‖
        = ‖((((involSaddleB3Real r) ^ 4 : ℝ) : ℂ) /
            (31104 * (involSaddleBReal r : ℂ) ^ 6))‖ * |x| ^ 12 := by
          rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (1 / r ^ 3) * |x| ^ 12 :=
          mul_le_mul_of_nonneg_right hcoef (pow_nonneg (abs_nonneg x) 12)
    _ ≤ 10 * |x| ^ 12 / r ^ 3 := by
          have hr3pos : 0 < r ^ 3 := by positivity
          field_simp [hr3pos.ne']
          nlinarith [pow_nonneg (abs_nonneg x) 12]

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

private lemma invol_third_extra_norm_le {r x : ℝ} (hr : 1 ≤ r) :
    ‖saddleThirdPoly involSaddleBReal involSaddleB3Real involSaddleB4Real
        involSaddleB5Real involSaddleB6Real r x -
      saddleSecondPoly involSaddleBReal involSaddleB3Real involSaddleB4Real r x‖
      ≤ 1000 * (|x| ^ 5 + |x| ^ 6 + |x| ^ 7 + |x| ^ 8 +
        |x| ^ 9 + |x| ^ 10 + |x| ^ 12) / r ^ 3 := by
  let T5 : ℂ :=
    Complex.I * ((involSaddleB5Real r : ℂ) /
      (120 * (Real.sqrt (involSaddleBReal r) : ℂ) ^ 5)) * (x : ℂ) ^ 5
  let T6 : ℂ :=
    -((involSaddleB6Real r : ℂ) / (720 * (involSaddleBReal r : ℂ) ^ 3)) *
      (x : ℂ) ^ 6
  let T7 : ℂ :=
    -Complex.I * (((involSaddleB3Real r * involSaddleB4Real r : ℝ) : ℂ) /
      (144 * (Real.sqrt (involSaddleBReal r) : ℂ) ^ 3 *
        (involSaddleBReal r : ℂ) ^ 2)) * (x : ℂ) ^ 7
  let T8a : ℂ :=
    (((involSaddleB3Real r * involSaddleB5Real r : ℝ) : ℂ) /
      (720 * (involSaddleBReal r : ℂ) ^ 4)) * (x : ℂ) ^ 8
  let T8b : ℂ :=
    ((((involSaddleB4Real r) ^ 2 : ℝ) : ℂ) /
      (1152 * (involSaddleBReal r : ℂ) ^ 4)) * (x : ℂ) ^ 8
  let T9 : ℂ :=
    Complex.I * ((((involSaddleB3Real r) ^ 3 : ℝ) : ℂ) /
      (1296 * (Real.sqrt (involSaddleBReal r) : ℂ) ^ 9)) * (x : ℂ) ^ 9
  let T10 : ℂ :=
    -(((((involSaddleB3Real r) ^ 2 * involSaddleB4Real r : ℝ) : ℂ) /
      (1728 * (involSaddleBReal r : ℂ) ^ 5)) * (x : ℂ) ^ 10)
  let T12 : ℂ :=
    ((((involSaddleB3Real r) ^ 4 : ℝ) : ℂ) /
      (31104 * (involSaddleBReal r : ℂ) ^ 6)) * (x : ℂ) ^ 12
  have h5 : ‖T5‖ ≤ 10 * |x| ^ 5 / r ^ 3 := by
    dsimp [T5]
    exact invol_third_extra5_norm_le (r := r) (x := x) hr
  have h6 : ‖T6‖ ≤ 10 * |x| ^ 6 / r ^ 3 := by
    dsimp [T6]
    simpa using invol_third_extra6_norm_le (r := r) (x := x) hr
  have h7 : ‖T7‖ ≤ 10 * |x| ^ 7 / r ^ 3 := by
    dsimp [T7]
    simpa [norm_neg] using invol_third_extra7_norm_le (r := r) (x := x) hr
  have h8a : ‖T8a‖ ≤ 10 * |x| ^ 8 / r ^ 3 := by
    dsimp [T8a]
    exact invol_third_extra8a_norm_le (r := r) (x := x) hr
  have h8b : ‖T8b‖ ≤ 10 * |x| ^ 8 / r ^ 3 := by
    dsimp [T8b]
    exact invol_third_extra8b_norm_le (r := r) (x := x) hr
  have h9 : ‖T9‖ ≤ 10 * |x| ^ 9 / r ^ 3 := by
    dsimp [T9]
    exact invol_third_extra9_norm_le (r := r) (x := x) hr
  have h10 : ‖T10‖ ≤ 10 * |x| ^ 10 / r ^ 3 := by
    dsimp [T10]
    simpa [norm_neg] using invol_third_extra10_norm_le (r := r) (x := x) hr
  have h12 : ‖T12‖ ≤ 10 * |x| ^ 12 / r ^ 3 := by
    dsimp [T12]
    exact invol_third_extra12_norm_le (r := r) (x := x) hr
  have hdiff :
      saddleThirdPoly involSaddleBReal involSaddleB3Real involSaddleB4Real
          involSaddleB5Real involSaddleB6Real r x -
        saddleSecondPoly involSaddleBReal involSaddleB3Real involSaddleB4Real r x =
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
    _ ≤ 10 * |x| ^ 5 / r ^ 3 + 10 * |x| ^ 6 / r ^ 3 +
          10 * |x| ^ 7 / r ^ 3 + 10 * |x| ^ 8 / r ^ 3 +
          10 * |x| ^ 8 / r ^ 3 + 10 * |x| ^ 9 / r ^ 3 +
          10 * |x| ^ 10 / r ^ 3 + 10 * |x| ^ 12 / r ^ 3 := by
          nlinarith
    _ ≤ 1000 * (|x| ^ 5 + |x| ^ 6 + |x| ^ 7 + |x| ^ 8 +
          |x| ^ 9 + |x| ^ 10 + |x| ^ 12) / r ^ 3 := by
          have hr3pos : 0 < r ^ 3 := by positivity
          field_simp [hr3pos.ne']
          nlinarith [hnonneg, pow_nonneg (abs_nonneg x) 5,
            pow_nonneg (abs_nonneg x) 6, pow_nonneg (abs_nonneg x) 7,
            pow_nonneg (abs_nonneg x) 8, pow_nonneg (abs_nonneg x) 9,
            pow_nonneg (abs_nonneg x) 10, pow_nonneg (abs_nonneg x) 12]

private lemma invol_local_third_extra_L1 :
    Tendsto
      (fun r : ℝ =>
        (∫ x in -(involSaddleDeltaReal r * Real.sqrt (involSaddleBReal r))..
          (involSaddleDeltaReal r * Real.sqrt (involSaddleBReal r)),
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleThirdPoly involSaddleBReal involSaddleB3Real involSaddleB4Real
              involSaddleB5Real involSaddleB6Real r x -
              saddleSecondPoly involSaddleBReal involSaddleB3Real involSaddleB4Real r x)‖) /
          involSecondCorrScale r)
      atTop (𝓝 0) := by
  let M : ℝ := ∫ x : ℝ, involThirdGaussianDom x
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact involThirdGaussianDom_integral_nonneg
  have hupper_tendsto :
      Tendsto (fun r : ℝ => (1000 * M * (27 / 16 : ℝ)) / r)
        atTop (𝓝 0) := by
    have hinv : Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero
    simpa [div_eq_mul_inv, mul_assoc] using
      hinv.const_mul (1000 * M * (27 / 16 : ℝ))
  refine squeeze_zero' ?_ ?_ hupper_tendsto
  · filter_upwards [eventually_ge_atTop (1 : ℝ), involSecondCorrScale_pos_eventually] with
      r hr hcorr
    let L : ℝ := involSaddleDeltaReal r * Real.sqrt (involSaddleBReal r)
    have hLnonneg : 0 ≤ L := by
      dsimp [L, involSaddleDeltaReal]
      positivity
    have hle : -L ≤ L := by linarith
    have hint_nonneg :
        0 ≤ ∫ x in -L..L,
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleThirdPoly involSaddleBReal involSaddleB3Real involSaddleB4Real
              involSaddleB5Real involSaddleB6Real r x -
              saddleSecondPoly involSaddleBReal involSaddleB3Real involSaddleB4Real r x)‖ :=
      intervalIntegral.integral_nonneg hle (fun _ _ => norm_nonneg _)
    exact div_nonneg hint_nonneg hcorr.le
  · filter_upwards [eventually_ge_atTop (1 : ℝ), involSecondCorrScale_lower_eventually,
      involSecondCorrScale_pos_eventually] with r hr hcorrLower hcorrPos
    let L : ℝ := involSaddleDeltaReal r * Real.sqrt (involSaddleBReal r)
    let F : ℝ → ℝ := fun x =>
      ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleThirdPoly involSaddleBReal involSaddleB3Real involSaddleB4Real
          involSaddleB5Real involSaddleB6Real r x -
          saddleSecondPoly involSaddleBReal involSaddleB3Real involSaddleB4Real r x)‖
    let G : ℝ → ℝ := fun x => (1000 / r ^ 3) * involThirdGaussianDom x
    have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
    have hLnonneg : 0 ≤ L := by
      dsimp [L, involSaddleDeltaReal]
      positivity
    have hle : -L ≤ L := by linarith
    have hpoint : ∀ x ∈ Set.Icc (-L) L, F x ≤ G x := by
      intro x hx
      have hdiff := invol_third_extra_norm_le (r := r) (x := x) hr
      dsimp [F, G, involThirdGaussianDom]
      rw [norm_mul]
      have hgauss :
          ‖Complex.exp (-(x ^ 2) / 2)‖ = Real.exp (-(x ^ 2) / 2) := by
        rw [Complex.norm_exp]
        congr 1
        simp [pow_two]
      rw [hgauss]
      calc
        Real.exp (-(x ^ 2) / 2) *
            ‖saddleThirdPoly involSaddleBReal involSaddleB3Real involSaddleB4Real
                involSaddleB5Real involSaddleB6Real r x -
              saddleSecondPoly involSaddleBReal involSaddleB3Real involSaddleB4Real r x‖
            ≤ Real.exp (-(x ^ 2) / 2) *
                (1000 * (|x| ^ 5 + |x| ^ 6 + |x| ^ 7 + |x| ^ 8 +
                  |x| ^ 9 + |x| ^ 10 + |x| ^ 12) / r ^ 3) :=
              mul_le_mul_of_nonneg_left hdiff (Real.exp_pos _).le
        _ = 1000 / r ^ 3 *
            (Real.exp (-(x ^ 2) / 2) *
              (|x| ^ 5 + |x| ^ 6 + |x| ^ 7 + |x| ^ 8 +
                |x| ^ 9 + |x| ^ 10 + |x| ^ 12)) := by ring
    have hFint : IntervalIntegrable F volume (-L) L := by
      have hcont : Continuous F := by
        dsimp [F]
        simp only [saddleThirdPoly, saddleSecondPoly, involSaddleBReal, involSaddleB3Real,
          involSaddleB4Real, involSaddleB5Real, involSaddleB6Real]
        fun_prop
      exact hcont.intervalIntegrable _ _
    have hGint : IntervalIntegrable G volume (-L) L := by
      exact (involThirdGaussianDom_continuous.const_mul (1000 / r ^ 3)).intervalIntegrable _ _
    have hIntBound :
        (∫ x in -L..L, F x) ≤ (1000 / r ^ 3) * M := by
      calc
        (∫ x in -L..L, F x) ≤ ∫ x in -L..L, G x :=
          intervalIntegral.integral_mono_on hle hFint hGint hpoint
        _ = (1000 / r ^ 3) * (∫ x in -L..L, involThirdGaussianDom x) := by
          dsimp [G]
          rw [intervalIntegral.integral_const_mul]
        _ ≤ (1000 / r ^ 3) * M := by
          exact mul_le_mul_of_nonneg_left
            (by dsimp [M]; exact involThirdGaussianDom_window_le_integral hLnonneg)
            (div_nonneg (by norm_num) (by positivity))
    have hnum_nonneg : 0 ≤ (1000 / r ^ 3) * M :=
      mul_nonneg (div_nonneg (by norm_num) (by positivity)) hM_nonneg
    have hscale_pos : 0 < (16 / 27 : ℝ) * r ^ (-(2 : ℝ)) := by positivity
    have hmain :
        (∫ x in -L..L, F x) / involSecondCorrScale r ≤
          ((1000 / r ^ 3) * M) / ((16 / 27 : ℝ) * r ^ (-(2 : ℝ))) := by
      calc
        (∫ x in -L..L, F x) / involSecondCorrScale r
            ≤ ((1000 / r ^ 3) * M) / involSecondCorrScale r :=
              div_le_div_of_nonneg_right hIntBound hcorrPos.le
        _ ≤ ((1000 / r ^ 3) * M) / ((16 / 27 : ℝ) * r ^ (-(2 : ℝ))) :=
            div_le_div_of_nonneg_left hnum_nonneg hscale_pos hcorrLower
    calc
      ((∫ x in -(involSaddleDeltaReal r * Real.sqrt (involSaddleBReal r))..
          (involSaddleDeltaReal r * Real.sqrt (involSaddleBReal r)),
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleThirdPoly involSaddleBReal involSaddleB3Real involSaddleB4Real
              involSaddleB5Real involSaddleB6Real r x -
              saddleSecondPoly involSaddleBReal involSaddleB3Real involSaddleB4Real r x)‖) /
          involSecondCorrScale r)
          = (∫ x in -L..L, F x) / involSecondCorrScale r := by rfl
      _ ≤ ((1000 / r ^ 3) * M) / ((16 / 27 : ℝ) * r ^ (-(2 : ℝ))) := hmain
      _ = (1000 * M * (27 / 16 : ℝ)) / r := by
        rw [Real.rpow_neg hrpos.le]
        field_simp [hrpos.ne']
        ring_nf
        norm_num

theorem invol_local_third_L1 :
    Tendsto
      (fun r : ℝ =>
        (∫ x in -(involSaddleDeltaReal r * Real.sqrt (involSaddleBReal r))..
          (involSaddleDeltaReal r * Real.sqrt (involSaddleBReal r)),
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleLocalRatio involFun involSaddleAReal involSaddleBReal r
                (x / Real.sqrt (involSaddleBReal r)) -
              saddleThirdPoly involSaddleBReal involSaddleB3Real involSaddleB4Real
                involSaddleB5Real involSaddleB6Real r x)‖) /
          involThirdCorrScale r)
      atTop (𝓝 0) := by
  unfold involThirdCorrScale
  let T : ℝ → ℝ := fun r =>
    (∫ x in -(involSaddleDeltaReal r * Real.sqrt (involSaddleBReal r))..
      (involSaddleDeltaReal r * Real.sqrt (involSaddleBReal r)),
      ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleLocalRatio involFun involSaddleAReal involSaddleBReal r
            (x / Real.sqrt (involSaddleBReal r)) -
          saddleThirdPoly involSaddleBReal involSaddleB3Real involSaddleB4Real
            involSaddleB5Real involSaddleB6Real r x)‖) / involSecondCorrScale r
  let S : ℝ → ℝ := fun r =>
    (∫ x in -(involSaddleDeltaReal r * Real.sqrt (involSaddleBReal r))..
      (involSaddleDeltaReal r * Real.sqrt (involSaddleBReal r)),
      ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleLocalRatio involFun involSaddleAReal involSaddleBReal r
            (x / Real.sqrt (involSaddleBReal r)) -
          saddleSecondPoly involSaddleBReal involSaddleB3Real involSaddleB4Real r x)‖) /
      involSecondCorrScale r
  let E : ℝ → ℝ := fun r =>
    (∫ x in -(involSaddleDeltaReal r * Real.sqrt (involSaddleBReal r))..
      (involSaddleDeltaReal r * Real.sqrt (involSaddleBReal r)),
      ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleThirdPoly involSaddleBReal involSaddleB3Real involSaddleB4Real
          involSaddleB5Real involSaddleB6Real r x -
          saddleSecondPoly involSaddleBReal involSaddleB3Real involSaddleB4Real r x)‖) /
      involSecondCorrScale r
  change Tendsto T atTop (𝓝 0)
  have hsecond := invol_local_second_L1
  have hextra := invol_local_third_extra_L1
  have hsum : Tendsto (fun r : ℝ => S r + E r) atTop (𝓝 0) := by
    simpa [S, E] using hsecond.add hextra
  refine squeeze_zero' ?_ ?_ hsum
  · filter_upwards [eventually_ge_atTop (1 : ℝ), involSecondCorrScale_pos_eventually] with
      r hr hcorr
    let L : ℝ := involSaddleDeltaReal r * Real.sqrt (involSaddleBReal r)
    have hLnonneg : 0 ≤ L := by
      dsimp [L, involSaddleDeltaReal]
      positivity
    have hle : -L ≤ L := by linarith
    have hint_nonneg :
        0 ≤ ∫ x in -L..L,
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleLocalRatio involFun involSaddleAReal involSaddleBReal r
                (x / Real.sqrt (involSaddleBReal r)) -
              saddleThirdPoly involSaddleBReal involSaddleB3Real involSaddleB4Real
                involSaddleB5Real involSaddleB6Real r x)‖ :=
      intervalIntegral.integral_nonneg hle (fun _ _ => norm_nonneg _)
    dsimp [T]
    exact div_nonneg hint_nonneg hcorr.le
  · filter_upwards [eventually_ge_atTop (1 : ℝ), involSecondCorrScale_pos_eventually] with
      r hr hcorr
    let L : ℝ := involSaddleDeltaReal r * Real.sqrt (involSaddleBReal r)
    let FT : ℝ → ℝ := fun x =>
      ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleLocalRatio involFun involSaddleAReal involSaddleBReal r
            (x / Real.sqrt (involSaddleBReal r)) -
          saddleThirdPoly involSaddleBReal involSaddleB3Real involSaddleB4Real
            involSaddleB5Real involSaddleB6Real r x)‖
    let FS : ℝ → ℝ := fun x =>
      ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleLocalRatio involFun involSaddleAReal involSaddleBReal r
            (x / Real.sqrt (involSaddleBReal r)) -
          saddleSecondPoly involSaddleBReal involSaddleB3Real involSaddleB4Real r x)‖
    let FE : ℝ → ℝ := fun x =>
      ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleThirdPoly involSaddleBReal involSaddleB3Real involSaddleB4Real
          involSaddleB5Real involSaddleB6Real r x -
          saddleSecondPoly involSaddleBReal involSaddleB3Real involSaddleB4Real r x)‖
    have hLnonneg : 0 ≤ L := by
      dsimp [L, involSaddleDeltaReal]
      positivity
    have hle : -L ≤ L := by linarith
    have hpoint : ∀ x ∈ Set.Icc (-L) L, FT x ≤ FS x + FE x := by
      intro x hx
      dsimp [FT, FS, FE]
      calc
        ‖Complex.exp (-(x ^ 2) / 2) *
          (saddleLocalRatio involFun involSaddleAReal involSaddleBReal r
              (x / Real.sqrt (involSaddleBReal r)) -
            saddleThirdPoly involSaddleBReal involSaddleB3Real involSaddleB4Real
              involSaddleB5Real involSaddleB6Real r x)‖
            =
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleLocalRatio involFun involSaddleAReal involSaddleBReal r
                (x / Real.sqrt (involSaddleBReal r)) -
              saddleSecondPoly involSaddleBReal involSaddleB3Real involSaddleB4Real r x) -
            Complex.exp (-(x ^ 2) / 2) *
              (saddleThirdPoly involSaddleBReal involSaddleB3Real involSaddleB4Real
                involSaddleB5Real involSaddleB6Real r x -
                saddleSecondPoly involSaddleBReal involSaddleB3Real involSaddleB4Real r x)‖ := by
              congr 1
              ring
        _ ≤
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleLocalRatio involFun involSaddleAReal involSaddleBReal r
                (x / Real.sqrt (involSaddleBReal r)) -
              saddleSecondPoly involSaddleBReal involSaddleB3Real involSaddleB4Real r x)‖ +
          ‖Complex.exp (-(x ^ 2) / 2) *
              (saddleThirdPoly involSaddleBReal involSaddleB3Real involSaddleB4Real
                involSaddleB5Real involSaddleB6Real r x -
                saddleSecondPoly involSaddleBReal involSaddleB3Real involSaddleB4Real r x)‖ :=
            norm_sub_le _ _
    have hFTint : IntervalIntegrable FT volume (-L) L := by
      have hcont : Continuous FT := by
        dsimp [FT]
        simp only [invol_saddleLocalRatio_eq]
        simp only [saddleThirdPoly, saddleSecondPoly, involLocalExponent,
          ExpStirling.expLocalRemainder, involFun, involSaddleAReal,
          involSaddleBReal, involSaddleB3Real, involSaddleB4Real, involSaddleB5Real,
          involSaddleB6Real]
        fun_prop
      exact hcont.intervalIntegrable _ _
    have hFSint : IntervalIntegrable FS volume (-L) L := by
      have hcont : Continuous FS := by
        dsimp [FS]
        simp only [invol_saddleLocalRatio_eq]
        simp only [saddleSecondPoly, involLocalExponent, ExpStirling.expLocalRemainder,
          involFun, involSaddleAReal, involSaddleBReal, involSaddleB3Real,
          involSaddleB4Real]
        fun_prop
      exact hcont.intervalIntegrable _ _
    have hFEint : IntervalIntegrable FE volume (-L) L := by
      have hcont : Continuous FE := by
        dsimp [FE]
        simp only [saddleThirdPoly, saddleSecondPoly, involSaddleBReal, involSaddleB3Real,
          involSaddleB4Real, involSaddleB5Real, involSaddleB6Real]
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
        (∫ x in -L..L, FT x) / involSecondCorrScale r ≤
          ((∫ x in -L..L, FS x) + (∫ x in -L..L, FE x)) /
            involSecondCorrScale r :=
      div_le_div_of_nonneg_right hInt hcorr.le
    calc
      T r = (∫ x in -L..L, FT x) / involSecondCorrScale r := by rfl
      _ ≤ ((∫ x in -L..L, FS x) + (∫ x in -L..L, FE x)) /
            involSecondCorrScale r := hdiv
      _ = S r + E r := by
        dsimp [S, E, FS, FE, L]
        ring

def involThirdOrderHAdmissible :
    ThirdOrderHAdmissible involHAdmissible involSecondOrderHAdmissible where
  b5 := involSaddleB5Real
  b6 := involSaddleB6Real
  corrScale3 := involThirdCorrScale
  corrScale3_pos := by
    simpa [involHAdmissible, involThirdCorrScale] using involSecondCorrScale_pos_eventually
  corrScale3_tendsto_zero := by
    simpa [involHAdmissible, involThirdCorrScale] using involSecondCorrScale_tendsto_zero
  corrScale3_dominates_correction := by
    simpa [involHAdmissible, involThirdCorrScale, involSecondOrderHAdmissible_b3,
      involSecondOrderHAdmissible_b4] using invol_saddleThirdCorrectionScale_le_second
  local_third_L1 := by
    simpa [involHAdmissible, involThirdCorrScale, involSecondOrderHAdmissible_b3,
      involSecondOrderHAdmissible_b4] using invol_local_third_L1
  tail_third_uniform := by
    simpa [involHAdmissible, involThirdCorrScale] using invol_tail_second_uniform

theorem invol_coeff_thirdOrder_saddle_from_HAdmissible :
    (fun n : ℕ =>
      involSeries.coeff n / involSecondOrderSaddleScale n -
        (1 + (saddleCorrection involSaddleBReal involSaddleB3Real involSaddleB4Real
          (involSaddleRadius n) : ℂ) +
          (saddleThirdCorrection involSaddleBReal involSaddleB3Real involSaddleB4Real
            involSaddleB5Real involSaddleB6Real (involSaddleRadius n) : ℂ)))
      =o[atTop]
    (fun n : ℕ => (involThirdCorrScale (involSaddleRadius n) : ℂ)) := by
  have h :=
    coeff_thirdOrder_saddle
      involHAdmissible involSecondOrderHAdmissible involThirdOrderHAdmissible
      involHAdmissibleSaddleSequence
  simpa [involSecondOrderSaddleScale, HAdmissible.B, involHAdmissible,
    involHAdmissibleSaddleSequence, involSecondOrderHAdmissible_b3,
    involSecondOrderHAdmissible_b4, involThirdCorrScale] using h

/--
Third-order saddle ratio for involutions:
`[z^n] exp(z+z^2/2)` divided by the saddle scale is
`1 + δ₁(r_n) + δ₂(r_n) + o(corrScale)`, with the exact third correction
`δ₂ = saddleThirdCorrection ...`.
-/
theorem involution_count_over_factorial_thirdOrder :
    (fun n : ℕ =>
      involCoeffC n / involSecondOrderSaddleScale n -
        (1 + (saddleCorrection involSaddleBReal involSaddleB3Real involSaddleB4Real
          (involSaddleRadius n) : ℂ) +
          (saddleThirdCorrection involSaddleBReal involSaddleB3Real involSaddleB4Real
            involSaddleB5Real involSaddleB6Real (involSaddleRadius n) : ℂ)))
      =o[atTop]
    (fun n : ℕ => (involThirdCorrScale (involSaddleRadius n) : ℂ)) := by
  refine invol_coeff_thirdOrder_saddle_from_HAdmissible.congr_left ?_
  intro n
  simp [involCoeffC, involSeries, PowerSeries.coeff_toFMLS, involCarrier_coeff]

end InvolutionHAdmissible
