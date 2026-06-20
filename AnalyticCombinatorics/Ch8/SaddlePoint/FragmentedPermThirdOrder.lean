import AnalyticCombinatorics.Ch8.SaddlePoint.FragmentedPermSecondOrder
import AnalyticCombinatorics.Ch8.SaddlePoint.ThirdOrderHAdmissible

/-!
# Third-order saddle data for fragmented permutations

This file adds the finite-radius third-order correction layer for
`exp (z / (1 - z))`.  The proof uses the narrower finite-radius window
`(1-r)^(29/20)`, because the second-order window is too wide for an
`o((1-r)^2)` third-order remainder.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval PowerSeries

set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

noncomputable section

namespace FragmentedPermHAdmissible

/-- Fifth logarithmic saddle derivative for fragmented permutations. -/
def fragPermSaddleB5Real (r : ℝ) : ℝ :=
  r * (1 + 26 * r + 66 * r ^ 2 + 26 * r ^ 3 + r ^ 4) / (1 - r) ^ 6

/-- Sixth logarithmic saddle derivative for fragmented permutations. -/
def fragPermSaddleB6Real (r : ℝ) : ℝ :=
  r * (1 + r) * (1 + 56 * r + 246 * r ^ 2 + 56 * r ^ 3 + r ^ 4) /
    (1 - r) ^ 7

/-- Narrow finite-radius window for the third-order fragmented-permutation proof. -/
def fragPermThirdSaddleDeltaReal (r : ℝ) : ℝ :=
  (1 - r) ^ (29 / 20 : ℝ)

/-- True third-order correction scale for the finite-radius fragmented-permutation saddle. -/
def fragPermThirdCorrScale (r : ℝ) : ℝ :=
  (1 - r) ^ 2

/-- Complex saddle scale used by the fragmented-permutation third-order statement. -/
def fragPermThirdOrderSaddleScale (n : ℕ) : ℂ :=
  saddleScale fragPermFun fragPermSaddleRadius
    (fun n => fragPermSaddleBReal (fragPermSaddleRadius n)) n

/-- The explicit third-order correction at the saddle radius. -/
def fragPermThirdCorrectionAtSaddle (n : ℕ) : ℝ :=
  saddleThirdCorrection fragPermSaddleBReal fragPermSaddleB3Real fragPermSaddleB4Real
    fragPermSaddleB5Real fragPermSaddleB6Real (fragPermSaddleRadius n)

/-- Error term for the fragmented-permutation EGF coefficient through third order. -/
def fragPermThirdOrderSeriesError (n : ℕ) : ℂ :=
  fragPermSeries.coeff n / fragPermThirdOrderSaddleScale n -
    (1 + (fragPermSecondCorrectionAtSaddle n : ℂ) +
      (fragPermThirdCorrectionAtSaddle n : ℂ))

lemma fragPermThirdCorrScale_pos_eventually :
    ∀ᶠ r : ℝ in fragPermRadFilter, 0 < fragPermThirdCorrScale r := by
  filter_upwards [fragPerm_eventually_Ioo_zero_one] with r hr
  unfold fragPermThirdCorrScale
  exact sq_pos_of_pos (by linarith [hr.2] : 0 < 1 - r)

lemma fragPermThirdCorrScale_tendsto_zero :
    Tendsto fragPermThirdCorrScale fragPermRadFilter (𝓝 0) := by
  have h :
      Tendsto (fun r : ℝ => 1 - r) fragPermRadFilter (𝓝 (0 : ℝ)) :=
    fragPerm_one_sub_tendsto_nhdsGT_zero.mono_right
      (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Set.Ioi (0 : ℝ)))
  simpa [fragPermThirdCorrScale] using h.pow 2

lemma fragPerm_one_sub_rpow_neg_one_twentieth_tendsto_atTop :
    Tendsto (fun r : ℝ => (1 - r) ^ (-(1 / 20 : ℝ))) fragPermRadFilter atTop := by
  have hinv : Tendsto (fun r : ℝ => (1 - r)⁻¹) fragPermRadFilter atTop :=
    tendsto_inv_nhdsGT_zero.comp fragPerm_one_sub_tendsto_nhdsGT_zero
  have hpow : Tendsto (fun r : ℝ => ((1 - r)⁻¹) ^ (1 / 20 : ℝ))
      fragPermRadFilter atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 20)).comp hinv
  refine Tendsto.congr' ?_ hpow
  filter_upwards [fragPerm_eventually_Ioo_zero_one] with r hr
  have hnonneg : 0 ≤ 1 - r := by linarith [hr.2]
  rw [Real.inv_rpow hnonneg]
  rw [← Real.rpow_neg hnonneg]

lemma fragPerm_third_delta_pos_eventually :
    ∀ᶠ r : ℝ in fragPermRadFilter, 0 < fragPermThirdSaddleDeltaReal r := by
  filter_upwards [fragPerm_eventually_Ioo_zero_one] with r hr
  unfold fragPermThirdSaddleDeltaReal
  exact Real.rpow_pos_of_pos (by linarith [hr.2] : 0 < 1 - r) _

lemma fragPerm_third_delta_le_pi_eventually :
    ∀ᶠ r : ℝ in fragPermRadFilter, fragPermThirdSaddleDeltaReal r ≤ Real.pi := by
  filter_upwards [fragPerm_eventually_Ioo_zero_one] with r hr
  have hbase_nonneg : 0 ≤ 1 - r := by linarith [hr.2]
  have hbase_le_one : 1 - r ≤ 1 := by linarith [hr.1]
  have hδ_le_one : fragPermThirdSaddleDeltaReal r ≤ 1 := by
    unfold fragPermThirdSaddleDeltaReal
    exact Real.rpow_le_one hbase_nonneg hbase_le_one
      (by norm_num : (0 : ℝ) ≤ 29 / 20)
  have hpi : (1 : ℝ) ≤ Real.pi := by
    nlinarith [Real.one_le_pi_div_two]
  exact hδ_le_one.trans hpi

lemma fragPerm_third_delta_le_one_eventually :
    ∀ᶠ r : ℝ in fragPermRadFilter, fragPermThirdSaddleDeltaReal r ≤ 1 := by
  filter_upwards [fragPerm_eventually_Ioo_zero_one] with r hr
  have hbase_nonneg : 0 ≤ 1 - r := by linarith [hr.2]
  have hbase_le_one : 1 - r ≤ 1 := by linarith [hr.1]
  unfold fragPermThirdSaddleDeltaReal
  exact Real.rpow_le_one hbase_nonneg hbase_le_one
    (by norm_num : (0 : ℝ) ≤ 29 / 20)

lemma fragPerm_third_delta_le_second_delta_eventually :
    ∀ᶠ r : ℝ in fragPermRadFilter,
      fragPermThirdSaddleDeltaReal r ≤ fragPermSaddleDeltaReal r := by
  filter_upwards [fragPerm_eventually_Ioo_zero_one] with r hr
  have hu_pos : 0 < 1 - r := by linarith [hr.2]
  have hu_le_one : 1 - r ≤ 1 := by linarith [hr.1]
  unfold fragPermThirdSaddleDeltaReal fragPermSaddleDeltaReal
  exact Real.rpow_le_rpow_of_exponent_ge hu_pos hu_le_one
    (by norm_num : (7 / 5 : ℝ) ≤ 29 / 20)

lemma fragPerm_third_delta_le_one_sub_quarter_eventually :
    ∀ᶠ r : ℝ in fragPermRadFilter,
      fragPermThirdSaddleDeltaReal r ≤ (1 - r) / 4 := by
  filter_upwards [fragPerm_third_delta_le_second_delta_eventually,
    fragPerm_delta_le_one_sub_quarter_eventually] with r hle hbase
  exact hle.trans hbase

lemma fragPerm_third_delta_sq_le_one_sub_sq_eventually :
    ∀ᶠ r : ℝ in fragPermRadFilter,
      (fragPermThirdSaddleDeltaReal r) ^ 2 ≤ (1 - r) ^ 2 := by
  filter_upwards [fragPerm_eventually_Ioo_zero_one] with r hr
  have hu_pos : 0 < 1 - r := by linarith [hr.2]
  have hu_nonneg : 0 ≤ 1 - r := hu_pos.le
  have hu_le_one : 1 - r ≤ 1 := by linarith [hr.1]
  calc
    (fragPermThirdSaddleDeltaReal r) ^ 2 = (1 - r) ^ (29 / 10 : ℝ) := by
      unfold fragPermThirdSaddleDeltaReal
      rw [← Real.rpow_mul_natCast hu_nonneg (29 / 20 : ℝ) 2]
      norm_num
    _ ≤ (1 - r) ^ (2 : ℝ) := by
      exact Real.rpow_le_rpow_of_exponent_ge hu_pos hu_le_one
        (by norm_num : (2 : ℝ) ≤ 29 / 10)
    _ = (1 - r) ^ 2 := by norm_num [Real.rpow_natCast]

lemma fragPerm_third_delta_sqrt_b_tendsto_atTop :
    Tendsto
      (fun r : ℝ => fragPermThirdSaddleDeltaReal r *
        Real.sqrt (fragPermSaddleBReal r))
      fragPermRadFilter atTop := by
  have hbase :
      Tendsto (fun r : ℝ => (1 / 2 : ℝ) *
        (1 - r) ^ (-(1 / 20 : ℝ))) fragPermRadFilter atTop :=
    (fragPerm_one_sub_rpow_neg_one_twentieth_tendsto_atTop.const_mul_atTop
      (by norm_num : (0 : ℝ) < 1 / 2))
  refine tendsto_atTop_mono' fragPermRadFilter ?_ hbase
  filter_upwards [fragPerm_eventually_Ioo_half_one] with r hr
  have hu_pos : 0 < 1 - r := by linarith [hr.2]
  have hu_nonneg : 0 ≤ 1 - r := hu_pos.le
  have hsqrt := fragPerm_sqrt_b_lower_of_Ioo_half_one hr
  calc
    (1 / 2 : ℝ) * (1 - r) ^ (-(1 / 20 : ℝ))
        = fragPermThirdSaddleDeltaReal r *
            ((1 / 2 : ℝ) * (1 - r) ^ (-(3 / 2 : ℝ))) := by
          unfold fragPermThirdSaddleDeltaReal
          calc
            (1 / 2 : ℝ) * (1 - r) ^ (-(1 / 20 : ℝ))
                = (1 / 2 : ℝ) *
                    ((1 - r) ^ (29 / 20 : ℝ) *
                      (1 - r) ^ (-(3 / 2 : ℝ))) := by
                  rw [← Real.rpow_add hu_pos]
                  norm_num
            _ = (1 - r) ^ (29 / 20 : ℝ) *
                ((1 / 2 : ℝ) * (1 - r) ^ (-(3 / 2 : ℝ))) := by ring
    _ ≤ fragPermThirdSaddleDeltaReal r * Real.sqrt (fragPermSaddleBReal r) := by
          exact mul_le_mul_of_nonneg_left hsqrt
            (Real.rpow_nonneg hu_nonneg _)

lemma fragPermSaddleB5Real_nonneg_of_Ioo_zero_one {r : ℝ}
    (hr : r ∈ Set.Ioo (0 : ℝ) 1) :
    0 ≤ fragPermSaddleB5Real r := by
  unfold fragPermSaddleB5Real
  have hu_pos : 0 < 1 - r := by linarith [hr.2]
  have hr0 : 0 ≤ r := hr.1.le
  have hden : 0 < (1 - r) ^ 6 := pow_pos hu_pos _
  have hnum : 0 ≤ r * (1 + 26 * r + 66 * r ^ 2 + 26 * r ^ 3 + r ^ 4) := by
    positivity
  exact div_nonneg hnum hden.le

lemma fragPermSaddleB6Real_nonneg_of_Ioo_zero_one {r : ℝ}
    (hr : r ∈ Set.Ioo (0 : ℝ) 1) :
    0 ≤ fragPermSaddleB6Real r := by
  unfold fragPermSaddleB6Real
  have hu_pos : 0 < 1 - r := by linarith [hr.2]
  have hr0 : 0 ≤ r := hr.1.le
  have hden : 0 < (1 - r) ^ 7 := pow_pos hu_pos _
  have hnum :
      0 ≤ r * (1 + r) * (1 + 56 * r + 246 * r ^ 2 + 56 * r ^ 3 + r ^ 4) := by
    positivity
  exact div_nonneg hnum hden.le

lemma fragPerm_saddleThirdCorrection_eq_closed {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    saddleThirdCorrection fragPermSaddleBReal fragPermSaddleB3Real fragPermSaddleB4Real
        fragPermSaddleB5Real fragPermSaddleB6Real r =
      (r - 1) ^ 2 *
        (r ^ 8 + 4 * r ^ 7 + 28 * r ^ 6 - 524 * r ^ 5 + 442 * r ^ 4 -
          524 * r ^ 3 + 28 * r ^ 2 + 4 * r + 1) /
          (288 * r ^ 2 * (1 + r) ^ 6) := by
  have hu : 1 - r ≠ 0 := by linarith
  have hrne : r ≠ 0 := hr.ne'
  have h1r : 1 + r ≠ 0 := by positivity
  unfold saddleThirdCorrection fragPermSaddleBReal fragPermSaddleB3Real
    fragPermSaddleB4Real fragPermSaddleB5Real fragPermSaddleB6Real
  field_simp [hu, hrne, h1r]
  ring

lemma fragPerm_saddleCorrection_eq_closed {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    saddleCorrection fragPermSaddleBReal fragPermSaddleB3Real fragPermSaddleB4Real r =
      (r - 1) * (r ^ 4 + 2 * r ^ 3 + 12 * r ^ 2 + 2 * r + 1) /
        (12 * r * (1 + r) ^ 3) := by
  have hu : 1 - r ≠ 0 := by linarith
  have hrne : r ≠ 0 := hr.ne'
  have h1r : 1 + r ≠ 0 := by positivity
  unfold saddleCorrection fragPermSaddleBReal fragPermSaddleB3Real fragPermSaddleB4Real
  field_simp [hu, hrne, h1r]
  ring

lemma fragPerm_saddleThirdCorrectionScale_le_sq_eventually :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ᶠ r : ℝ in fragPermRadFilter,
        |fragPermSaddleB6Real r| / (fragPermSaddleBReal r) ^ 3
          + |fragPermSaddleB3Real r * fragPermSaddleB5Real r| /
              (fragPermSaddleBReal r) ^ 4
          + (fragPermSaddleB4Real r) ^ 2 / (fragPermSaddleBReal r) ^ 4
          + (fragPermSaddleB3Real r) ^ 2 * |fragPermSaddleB4Real r| /
              (fragPermSaddleBReal r) ^ 5
          + (fragPermSaddleB3Real r) ^ 4 / (fragPermSaddleBReal r) ^ 6
            ≤ K * fragPermThirdCorrScale r := by
  refine ⟨150000, by norm_num, ?_⟩
  filter_upwards [fragPerm_eventually_Ioo_half_one] with r hr
  let u : ℝ := 1 - r
  have hrpos : 0 < r := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hr.1
  have hr0 : 0 ≤ r := hrpos.le
  have hrle : r ≤ 1 := hr.2.le
  have hu_pos : 0 < u := by dsimp [u]; linarith [hr.2]
  have hu_nonneg : 0 ≤ u := hu_pos.le
  have hbpos : 0 < fragPermSaddleBReal r := by
    unfold fragPermSaddleBReal
    have hnum : 0 < r * (1 + r) := by positivity
    have hden : 0 < (1 - r) ^ 3 := by positivity
    exact div_pos hnum hden
  have hb3_nonneg : 0 ≤ fragPermSaddleB3Real r := by
    unfold fragPermSaddleB3Real
    positivity
  have hb4_nonneg : 0 ≤ fragPermSaddleB4Real r := by
    unfold fragPermSaddleB4Real
    positivity
  have hb5_nonneg : 0 ≤ fragPermSaddleB5Real r :=
    fragPermSaddleB5Real_nonneg_of_Ioo_zero_one
      ⟨lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hr.1, hr.2⟩
  have hb6_nonneg : 0 ≤ fragPermSaddleB6Real r :=
    fragPermSaddleB6Real_nonneg_of_Ioo_zero_one
      ⟨lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hr.1, hr.2⟩
  have hB_lower : (1 / 2 : ℝ) / u ^ 3 ≤ fragPermSaddleBReal r := by
    unfold fragPermSaddleBReal
    dsimp [u]
    have hden_pos : 0 < (1 - r) ^ 3 := by positivity
    have hnum_ge : (1 / 2 : ℝ) ≤ r * (1 + r) := by nlinarith [hr.1]
    exact div_le_div_of_nonneg_right hnum_ge hden_pos.le
  have hB_inv_le : (fragPermSaddleBReal r)⁻¹ ≤ 2 * u ^ 3 := by
    have hlow_pos : 0 < (1 / 2 : ℝ) / u ^ 3 := by positivity
    have hmul := inv_anti₀ hlow_pos hB_lower
    calc
      (fragPermSaddleBReal r)⁻¹ ≤ ((1 / 2 : ℝ) / u ^ 3)⁻¹ := hmul
      _ = 2 * u ^ 3 := by field_simp [hu_pos.ne']
  have hpoly3_le : 1 + 4 * r + r ^ 2 ≤ 6 := by
    nlinarith [hr.1, hrle, sq_nonneg r, sq_nonneg (1 - r)]
  have hpoly4_le : 1 + 11 * r + 11 * r ^ 2 + r ^ 3 ≤ 24 := by
    nlinarith [hr.1, hrle, sq_nonneg r, sq_nonneg (1 - r), sq_nonneg (r - 1)]
  have hpoly5_le :
      1 + 26 * r + 66 * r ^ 2 + 26 * r ^ 3 + r ^ 4 ≤ 120 := by
    nlinarith [hr.1, hrle, sq_nonneg r, sq_nonneg (1 - r), sq_nonneg (r - 1),
      show 0 ≤ r ^ 3 by positivity, show 0 ≤ r ^ 4 by positivity]
  have hpoly6_le :
      1 + 56 * r + 246 * r ^ 2 + 56 * r ^ 3 + r ^ 4 ≤ 360 := by
    nlinarith [hr.1, hrle, sq_nonneg r, sq_nonneg (1 - r), sq_nonneg (r - 1),
      show 0 ≤ r ^ 3 by positivity, show 0 ≤ r ^ 4 by positivity]
  have hb3_le : fragPermSaddleB3Real r ≤ 6 / u ^ 4 := by
    unfold fragPermSaddleB3Real
    dsimp [u]
    have hden_pos : 0 < (1 - r) ^ 4 := by positivity
    calc
      r * (1 + 4 * r + r ^ 2) / (1 - r) ^ 4
          ≤ 1 * 6 / (1 - r) ^ 4 := by
            exact div_le_div_of_nonneg_right
              (mul_le_mul hrle hpoly3_le (by positivity) zero_le_one) hden_pos.le
      _ = 6 / u ^ 4 := by ring
  have hb4_le : fragPermSaddleB4Real r ≤ 24 / u ^ 5 := by
    unfold fragPermSaddleB4Real
    dsimp [u]
    have hden_pos : 0 < (1 - r) ^ 5 := by positivity
    calc
      r * (1 + 11 * r + 11 * r ^ 2 + r ^ 3) / (1 - r) ^ 5
          ≤ 1 * 24 / (1 - r) ^ 5 := by
            exact div_le_div_of_nonneg_right
              (mul_le_mul hrle hpoly4_le (by positivity) zero_le_one) hden_pos.le
      _ = 24 / u ^ 5 := by ring
  have hb5_le : fragPermSaddleB5Real r ≤ 120 / u ^ 6 := by
    unfold fragPermSaddleB5Real
    dsimp [u]
    have hden_pos : 0 < (1 - r) ^ 6 := by positivity
    calc
      r * (1 + 26 * r + 66 * r ^ 2 + 26 * r ^ 3 + r ^ 4) / (1 - r) ^ 6
          ≤ 1 * 120 / (1 - r) ^ 6 := by
            exact div_le_div_of_nonneg_right
              (mul_le_mul hrle hpoly5_le (by positivity) zero_le_one) hden_pos.le
      _ = 120 / u ^ 6 := by ring
  have hb6_le : fragPermSaddleB6Real r ≤ 720 / u ^ 7 := by
    unfold fragPermSaddleB6Real
    dsimp [u]
    have hden_pos : 0 < (1 - r) ^ 7 := by positivity
    have hnum_le :
        r * (1 + r) * (1 + 56 * r + 246 * r ^ 2 + 56 * r ^ 3 + r ^ 4) ≤
          2 * 360 := by
      have hr1_le_two : r * (1 + r) ≤ 2 := by nlinarith [hr.1, hrle]
      exact mul_le_mul hr1_le_two hpoly6_le (by positivity) (by positivity)
    calc
      r * (1 + r) * (1 + 56 * r + 246 * r ^ 2 + 56 * r ^ 3 + r ^ 4) /
          (1 - r) ^ 7
          ≤ 720 / (1 - r) ^ 7 := by
            exact div_le_div_of_nonneg_right (by nlinarith [hnum_le]) hden_pos.le
      _ = 720 / u ^ 7 := by dsimp [u]
  have hterm1 :
      |fragPermSaddleB6Real r| / (fragPermSaddleBReal r) ^ 3 ≤ 5760 * u ^ 2 := by
    rw [abs_of_nonneg hb6_nonneg]
    rw [div_eq_mul_inv, ← inv_pow]
    calc
      fragPermSaddleB6Real r * (fragPermSaddleBReal r)⁻¹ ^ 3
          ≤ (720 / u ^ 7) * (2 * u ^ 3) ^ 3 := by
            exact mul_le_mul hb6_le
              (pow_le_pow_left₀ (inv_nonneg.mpr hbpos.le) hB_inv_le 3)
              (by positivity) (by positivity)
      _ = 5760 * u ^ 2 := by field_simp [hu_pos.ne']; ring
  have hterm2 :
      |fragPermSaddleB3Real r * fragPermSaddleB5Real r| /
          (fragPermSaddleBReal r) ^ 4 ≤ 11520 * u ^ 2 := by
    rw [abs_of_nonneg (mul_nonneg hb3_nonneg hb5_nonneg)]
    rw [div_eq_mul_inv, ← inv_pow]
    have hnum :
        fragPermSaddleB3Real r * fragPermSaddleB5Real r ≤
          (6 / u ^ 4) * (120 / u ^ 6) :=
      mul_le_mul hb3_le hb5_le hb5_nonneg (by positivity)
    calc
      fragPermSaddleB3Real r * fragPermSaddleB5Real r *
            (fragPermSaddleBReal r)⁻¹ ^ 4
          ≤ ((6 / u ^ 4) * (120 / u ^ 6)) * (2 * u ^ 3) ^ 4 := by
            exact mul_le_mul hnum
              (pow_le_pow_left₀ (inv_nonneg.mpr hbpos.le) hB_inv_le 4)
              (by positivity) (by positivity)
      _ = 11520 * u ^ 2 := by field_simp [hu_pos.ne']; ring
  have hterm3 :
      (fragPermSaddleB4Real r) ^ 2 / (fragPermSaddleBReal r) ^ 4 ≤
          9216 * u ^ 2 := by
    rw [div_eq_mul_inv, ← inv_pow]
    have hnum : (fragPermSaddleB4Real r) ^ 2 ≤ (24 / u ^ 5) ^ 2 :=
      pow_le_pow_left₀ hb4_nonneg hb4_le 2
    calc
      (fragPermSaddleB4Real r) ^ 2 * (fragPermSaddleBReal r)⁻¹ ^ 4
          ≤ (24 / u ^ 5) ^ 2 * (2 * u ^ 3) ^ 4 := by
            exact mul_le_mul hnum
              (pow_le_pow_left₀ (inv_nonneg.mpr hbpos.le) hB_inv_le 4)
              (by positivity) (sq_nonneg _)
      _ = 9216 * u ^ 2 := by field_simp [hu_pos.ne']; ring
  have hterm4 :
      (fragPermSaddleB3Real r) ^ 2 * |fragPermSaddleB4Real r| /
          (fragPermSaddleBReal r) ^ 5 ≤ 27648 * u ^ 2 := by
    rw [abs_of_nonneg hb4_nonneg]
    rw [div_eq_mul_inv, ← inv_pow]
    have hnum :
        (fragPermSaddleB3Real r) ^ 2 * fragPermSaddleB4Real r ≤
          (6 / u ^ 4) ^ 2 * (24 / u ^ 5) :=
      mul_le_mul (pow_le_pow_left₀ hb3_nonneg hb3_le 2) hb4_le
        (by positivity) (sq_nonneg _)
    calc
      (fragPermSaddleB3Real r) ^ 2 * fragPermSaddleB4Real r *
            (fragPermSaddleBReal r)⁻¹ ^ 5
          ≤ ((6 / u ^ 4) ^ 2 * (24 / u ^ 5)) * (2 * u ^ 3) ^ 5 := by
            exact mul_le_mul hnum
              (pow_le_pow_left₀ (inv_nonneg.mpr hbpos.le) hB_inv_le 5)
              (by positivity) (by positivity)
      _ = 27648 * u ^ 2 := by field_simp [hu_pos.ne']; ring
  have hterm5 :
      (fragPermSaddleB3Real r) ^ 4 / (fragPermSaddleBReal r) ^ 6 ≤
          82944 * u ^ 2 := by
    rw [div_eq_mul_inv, ← inv_pow]
    have hnum : (fragPermSaddleB3Real r) ^ 4 ≤ (6 / u ^ 4) ^ 4 :=
      pow_le_pow_left₀ hb3_nonneg hb3_le 4
    calc
      (fragPermSaddleB3Real r) ^ 4 * (fragPermSaddleBReal r)⁻¹ ^ 6
          ≤ (6 / u ^ 4) ^ 4 * (2 * u ^ 3) ^ 6 := by
            exact mul_le_mul hnum
              (pow_le_pow_left₀ (inv_nonneg.mpr hbpos.le) hB_inv_le 6)
              (by positivity) (by positivity)
      _ = 82944 * u ^ 2 := by field_simp [hu_pos.ne']; ring
  unfold fragPermThirdCorrScale
  dsimp [u] at hterm1 hterm2 hterm3 hterm4 hterm5 ⊢
  nlinarith [hterm1, hterm2, hterm3, hterm4, hterm5]

/-- Near-tail envelope for the third-order finite-radius window. -/
def fragPermThirdNearTailE (r : ℝ) : ℝ :=
  2 * Real.exp (-(1 / 4 : ℝ) * (1 - r) ^ (-(1 / 10 : ℝ)))

/-- Combined third-order finite-radius tail envelope. -/
def fragPermThirdTailE (r : ℝ) : ℝ :=
  fragPermThirdNearTailE r + fragPermTailE r

lemma saddleGAt_norm_eq_gaussian_mul_saddleLocalRatio_norm
    (f : ℂ → ℂ) (a b : ℝ → ℝ) (r : ℝ) (n : ℕ) (θ : ℝ) :
    ‖saddleGAt f r n θ‖ =
      Real.exp (-(b r * θ ^ 2 / 2)) *
        ‖saddleLocalRatio f a b r θ‖ := by
  let A : ℂ := f ((r : ℂ) * Complex.exp (θ * Complex.I)) / f (r : ℂ)
  let Pn : ℂ := Complex.exp (-(↑↑n * ↑θ) * Complex.I)
  let Pa : ℂ := Complex.exp (-(a r * θ : ℝ) * Complex.I)
  let G : ℂ := Complex.exp (-(b r * θ ^ 2 / 2 : ℝ))
  have hPn : ‖Pn‖ = 1 := by
    dsimp [Pn]
    rw [Complex.norm_exp]
    simp
  have hPa : ‖Pa‖ = 1 := by
    dsimp [Pa]
    rw [Complex.norm_exp]
    simp
  have hGnorm : ‖G‖ = Real.exp (-(b r * θ ^ 2 / 2)) := by
    dsimp [G]
    rw [Complex.norm_exp]
    congr 1
  have hGpos : 0 < Real.exp (-(b r * θ ^ 2 / 2)) := Real.exp_pos _
  unfold saddleGAt saddleLocalRatio
  change ‖A * Pn‖ = Real.exp (-(b r * θ ^ 2 / 2)) * ‖A * Pa / G‖
  rw [norm_mul, hPn, mul_one]
  have hdivnorm : ‖A * Pa / G‖ = ‖A * Pa‖ / ‖G‖ := by
    rw [norm_div]
  rw [hdivnorm]
  rw [norm_mul, hPa, mul_one, hGnorm]
  field_simp [hGpos.ne']

lemma fragPermThirdNearTailE_nonneg_eventually :
    ∀ᶠ r : ℝ in fragPermRadFilter, 0 ≤ fragPermThirdNearTailE r :=
  Eventually.of_forall fun _ => by
    unfold fragPermThirdNearTailE
    positivity

lemma fragPermThirdTailE_nonneg_eventually :
    ∀ᶠ r : ℝ in fragPermRadFilter, 0 ≤ fragPermThirdTailE r := by
  filter_upwards [fragPermThirdNearTailE_nonneg_eventually,
    fragPermTailE_nonneg_eventually] with r hnear hfar
  unfold fragPermThirdTailE
  positivity

lemma fragPerm_one_sub_rpow_neg_one_tenth_tendsto_atTop :
    Tendsto (fun r : ℝ => (1 - r) ^ (-(1 / 10 : ℝ))) fragPermRadFilter atTop :=
  fragPerm_one_sub_rpow_neg_tendsto_atTop

lemma fragPermThirdNearTailE_decay :
    Tendsto
      (fun r : ℝ =>
        Real.sqrt (2 * Real.pi * fragPermSaddleBReal r) * fragPermThirdNearTailE r /
          fragPermThirdCorrScale r)
      fragPermRadFilter (𝓝 0) := by
  let c : ℝ := (1 / 4 : ℝ)
  have hc : 0 < c := by norm_num [c]
  have hbase :
      Tendsto (fun y : ℝ => y ^ (35 : ℝ) * Real.exp (-c * y))
        atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (35 : ℝ) c hc
  have hy := fragPerm_one_sub_rpow_neg_one_tenth_tendsto_atTop
  have hcomp :
      Tendsto
        (fun r : ℝ => ((1 - r) ^ (-(1 / 10 : ℝ))) ^ (35 : ℝ) *
          Real.exp (-c * ((1 - r) ^ (-(1 / 10 : ℝ)))))
        fragPermRadFilter (𝓝 0) :=
    hbase.comp hy
  have hscaled :
      Tendsto
        (fun r : ℝ => 2 * Real.sqrt (4 * Real.pi) *
          (((1 - r) ^ (-(1 / 10 : ℝ))) ^ (35 : ℝ) *
            Real.exp (-c * ((1 - r) ^ (-(1 / 10 : ℝ))))))
        fragPermRadFilter (𝓝 0) := by
    simpa using hcomp.const_mul (2 * Real.sqrt (4 * Real.pi))
  refine squeeze_zero' ?_ ?_ hscaled
  · filter_upwards [fragPermThirdCorrScale_pos_eventually] with r hcorr
    exact div_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) (by unfold fragPermThirdNearTailE; positivity))
      hcorr.le
  · filter_upwards [fragPerm_eventually_Ioo_half_one] with r hr
    let u : ℝ := 1 - r
    have hu_pos : 0 < u := by dsimp [u]; linarith [hr.2]
    have hu_nonneg : 0 ≤ u := hu_pos.le
    have hnum_le : r * (1 + r) ≤ 2 := by nlinarith [hr.1, hr.2]
    have hB_le : fragPermSaddleBReal r ≤ 2 / u ^ 3 := by
      unfold fragPermSaddleBReal
      dsimp [u]
      have hden_pos : 0 < (1 - r) ^ 3 := by positivity
      exact div_le_div_of_nonneg_right hnum_le hden_pos.le
    have hmul : 2 * Real.pi * fragPermSaddleBReal r ≤ 4 * Real.pi / u ^ 3 := by
      calc
        2 * Real.pi * fragPermSaddleBReal r
            ≤ 2 * Real.pi * (2 / u ^ 3) :=
              mul_le_mul_of_nonneg_left hB_le (by positivity)
        _ = 4 * Real.pi / u ^ 3 := by ring
    have hsqrt :
        Real.sqrt (2 * Real.pi * fragPermSaddleBReal r) ≤
          Real.sqrt (4 * Real.pi) * u ^ (-(3 / 2 : ℝ)) := by
      calc
        Real.sqrt (2 * Real.pi * fragPermSaddleBReal r)
            ≤ Real.sqrt (4 * Real.pi / u ^ 3) := Real.sqrt_le_sqrt hmul
        _ = Real.sqrt (4 * Real.pi) * u ^ (-(3 / 2 : ℝ)) := by
          have h4pi : 0 ≤ 4 * Real.pi := by positivity
          rw [div_eq_mul_inv]
          rw [Real.sqrt_mul h4pi]
          have hsqrt_inv_u3 : Real.sqrt ((u ^ 3)⁻¹) = u ^ (-(3 / 2 : ℝ)) := by
            have hinv_u3 : (u ^ 3)⁻¹ = u ^ (-3 : ℝ) := by
              rw [show u ^ 3 = u ^ (3 : ℝ) by exact (Real.rpow_natCast u 3).symm]
              rw [← Real.rpow_neg hu_nonneg (3 : ℝ)]
            rw [hinv_u3]
            rw [Real.sqrt_eq_rpow]
            rw [← Real.rpow_mul hu_nonneg]
            norm_num
          congr 1
    have hy_pow :
        ((1 - r) ^ (-(1 / 10 : ℝ))) ^ (35 : ℝ) =
          u ^ (-(7 / 2 : ℝ)) := by
      have h :
          ((1 - r) ^ (-(1 / 10 : ℝ))) ^ (35 : ℝ) =
            (1 - r) ^ (-(7 / 2 : ℝ)) := by
        rw [← Real.rpow_mul (by linarith : 0 ≤ 1 - r)]
        norm_num
      simpa [u] using h
    have hpow_div : u ^ (-(3 / 2 : ℝ)) / u ^ 2 = u ^ (-(7 / 2 : ℝ)) := by
      rw [show u ^ 2 = u ^ (2 : ℝ) by exact (Real.rpow_natCast u 2).symm]
      rw [div_eq_mul_inv]
      rw [← Real.rpow_neg hu_nonneg (2 : ℝ)]
      rw [← Real.rpow_add hu_pos]
      norm_num
    unfold fragPermThirdNearTailE fragPermThirdCorrScale
    dsimp [c]
    rw [hy_pow]
    calc
      Real.sqrt (2 * Real.pi * fragPermSaddleBReal r) *
            (2 * Real.exp (-(1 / 4 : ℝ) * (1 - r) ^ (-(1 / 10 : ℝ)))) /
          (1 - r) ^ 2
          ≤ (Real.sqrt (4 * Real.pi) * u ^ (-(3 / 2 : ℝ))) *
              (2 * Real.exp (-(1 / 4 : ℝ) * (1 - r) ^ (-(1 / 10 : ℝ)))) /
            u ^ 2 := by
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right hsqrt (by positivity))
              (by positivity)
      _ = 2 * Real.sqrt (4 * Real.pi) *
            (u ^ (-(7 / 2 : ℝ)) *
              Real.exp (-(1 / 4 : ℝ) * (1 - r) ^ (-(1 / 10 : ℝ)))) := by
            calc
              Real.sqrt (4 * Real.pi) * u ^ (-(3 / 2 : ℝ)) *
                    (2 * Real.exp (-(1 / 4 : ℝ) *
                      (1 - r) ^ (-(1 / 10 : ℝ)))) / u ^ 2
                  =
                    2 * Real.sqrt (4 * Real.pi) *
                      ((u ^ (-(3 / 2 : ℝ)) / u ^ 2) *
                        Real.exp (-(1 / 4 : ℝ) *
                          (1 - r) ^ (-(1 / 10 : ℝ)))) := by
                    field_simp [hu_pos.ne']
              _ = 2 * Real.sqrt (4 * Real.pi) *
                    (u ^ (-(7 / 2 : ℝ)) *
                      Real.exp (-(1 / 4 : ℝ) *
                        (1 - r) ^ (-(1 / 10 : ℝ)))) := by
                    rw [hpow_div]

lemma fragPermTailE_third_decay :
    Tendsto
      (fun r : ℝ =>
        Real.sqrt (2 * Real.pi * fragPermSaddleBReal r) * fragPermTailE r /
          fragPermThirdCorrScale r)
      fragPermRadFilter (𝓝 0) := by
  let c : ℝ := fragPermTailC
  have hc : 0 < c := by
    dsimp [c, fragPermTailC]
    positivity
  have hbase :
      Tendsto (fun y : ℝ => y ^ (35 / 2 : ℝ) * Real.exp (-c * y))
        atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (35 / 2 : ℝ) c hc
  have hy := fragPerm_one_sub_rpow_neg_one_fifth_tendsto_atTop
  have hcomp :
      Tendsto
        (fun r : ℝ => ((1 - r) ^ (-(1 / 5 : ℝ))) ^ (35 / 2 : ℝ) *
          Real.exp (-c * ((1 - r) ^ (-(1 / 5 : ℝ)))))
        fragPermRadFilter (𝓝 0) :=
    hbase.comp hy
  have hscaled :
      Tendsto
        (fun r : ℝ => Real.sqrt (4 * Real.pi) *
          (((1 - r) ^ (-(1 / 5 : ℝ))) ^ (35 / 2 : ℝ) *
            Real.exp (-c * ((1 - r) ^ (-(1 / 5 : ℝ))))))
        fragPermRadFilter (𝓝 0) := by
    simpa using hcomp.const_mul (Real.sqrt (4 * Real.pi))
  refine squeeze_zero' ?_ ?_ hscaled
  · filter_upwards [fragPermThirdCorrScale_pos_eventually] with r hcorr
    exact div_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le) hcorr.le
  · filter_upwards [fragPerm_eventually_Ioo_half_one] with r hr
    let u : ℝ := 1 - r
    have hu_pos : 0 < u := by dsimp [u]; linarith [hr.2]
    have hu_nonneg : 0 ≤ u := hu_pos.le
    have hnum_le : r * (1 + r) ≤ 2 := by nlinarith [hr.1, hr.2]
    have hB_le : fragPermSaddleBReal r ≤ 2 / u ^ 3 := by
      unfold fragPermSaddleBReal
      dsimp [u]
      have hden_pos : 0 < (1 - r) ^ 3 := by positivity
      exact div_le_div_of_nonneg_right hnum_le hden_pos.le
    have hmul : 2 * Real.pi * fragPermSaddleBReal r ≤ 4 * Real.pi / u ^ 3 := by
      calc
        2 * Real.pi * fragPermSaddleBReal r
            ≤ 2 * Real.pi * (2 / u ^ 3) :=
              mul_le_mul_of_nonneg_left hB_le (by positivity)
        _ = 4 * Real.pi / u ^ 3 := by ring
    have hsqrt :
        Real.sqrt (2 * Real.pi * fragPermSaddleBReal r) ≤
          Real.sqrt (4 * Real.pi) * u ^ (-(3 / 2 : ℝ)) := by
      calc
        Real.sqrt (2 * Real.pi * fragPermSaddleBReal r)
            ≤ Real.sqrt (4 * Real.pi / u ^ 3) := Real.sqrt_le_sqrt hmul
        _ = Real.sqrt (4 * Real.pi) * u ^ (-(3 / 2 : ℝ)) := by
          have h4pi : 0 ≤ 4 * Real.pi := by positivity
          rw [div_eq_mul_inv]
          rw [Real.sqrt_mul h4pi]
          have hsqrt_inv_u3 : Real.sqrt ((u ^ 3)⁻¹) = u ^ (-(3 / 2 : ℝ)) := by
            have hinv_u3 : (u ^ 3)⁻¹ = u ^ (-3 : ℝ) := by
              rw [show u ^ 3 = u ^ (3 : ℝ) by exact (Real.rpow_natCast u 3).symm]
              rw [← Real.rpow_neg hu_nonneg (3 : ℝ)]
            rw [hinv_u3]
            rw [Real.sqrt_eq_rpow]
            rw [← Real.rpow_mul hu_nonneg]
            norm_num
          congr 1
    have hy_pow :
        ((1 - r) ^ (-(1 / 5 : ℝ))) ^ (35 / 2 : ℝ) =
          u ^ (-(7 / 2 : ℝ)) := by
      have h :
          ((1 - r) ^ (-(1 / 5 : ℝ))) ^ (35 / 2 : ℝ) =
            (1 - r) ^ (-(7 / 2 : ℝ)) := by
        rw [← Real.rpow_mul (by linarith : 0 ≤ 1 - r)]
        norm_num
      simpa [u] using h
    have hpow_div : u ^ (-(3 / 2 : ℝ)) / u ^ 2 = u ^ (-(7 / 2 : ℝ)) := by
      rw [show u ^ 2 = u ^ (2 : ℝ) by exact (Real.rpow_natCast u 2).symm]
      rw [div_eq_mul_inv]
      rw [← Real.rpow_neg hu_nonneg (2 : ℝ)]
      rw [← Real.rpow_add hu_pos]
      norm_num
    unfold fragPermTailE fragPermThirdCorrScale
    dsimp [c, fragPermTailC]
    rw [hy_pow]
    calc
      Real.sqrt (2 * Real.pi * fragPermSaddleBReal r) *
            Real.exp (-(1 / (4 * Real.pi ^ 2)) *
              (1 - r) ^ (-(1 / 5 : ℝ))) / (1 - r) ^ 2
          ≤ (Real.sqrt (4 * Real.pi) * u ^ (-(3 / 2 : ℝ))) *
              Real.exp (-(1 / (4 * Real.pi ^ 2)) *
                (1 - r) ^ (-(1 / 5 : ℝ))) / u ^ 2 := by
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right hsqrt (Real.exp_pos _).le)
              (by positivity)
      _ = Real.sqrt (4 * Real.pi) *
            (u ^ (-(7 / 2 : ℝ)) *
              Real.exp (-(1 / (4 * Real.pi ^ 2)) *
                (1 - r) ^ (-(1 / 5 : ℝ)))) := by
            calc
              Real.sqrt (4 * Real.pi) * u ^ (-(3 / 2 : ℝ)) *
                    Real.exp (-(1 / (4 * Real.pi ^ 2)) *
                      (1 - r) ^ (-(1 / 5 : ℝ))) / u ^ 2
                  =
                    Real.sqrt (4 * Real.pi) *
                      ((u ^ (-(3 / 2 : ℝ)) / u ^ 2) *
                        Real.exp (-(1 / (4 * Real.pi ^ 2)) *
                          (1 - r) ^ (-(1 / 5 : ℝ)))) := by
                    field_simp [hu_pos.ne']
              _ = Real.sqrt (4 * Real.pi) *
                    (u ^ (-(7 / 2 : ℝ)) *
                      Real.exp (-(1 / (4 * Real.pi ^ 2)) *
                        (1 - r) ^ (-(1 / 5 : ℝ)))) := by
                    rw [hpow_div]

lemma fragPermThirdTailE_decay :
    Tendsto
      (fun r : ℝ =>
        Real.sqrt (2 * Real.pi * fragPermSaddleBReal r) * fragPermThirdTailE r /
          fragPermThirdCorrScale r)
      fragPermRadFilter (𝓝 0) := by
  have hnear := fragPermThirdNearTailE_decay
  have hfar := fragPermTailE_third_decay
  have hsum := hnear.add hfar
  simpa [fragPermThirdTailE, mul_add, add_div] using hsum

lemma fragPerm_third_tail_bound_eventually :
    ∀ᶠ r : ℝ in fragPermRadFilter, ∀ n : ℕ, ∀ θ : ℝ,
      fragPermThirdSaddleDeltaReal r ≤ |θ| → |θ| ≤ Real.pi →
        ‖saddleGAt fragPermFun r n θ‖ ≤ fragPermThirdTailE r := by
  have hlocal := fragPerm_local_uniform 1 (by norm_num : (0 : ℝ) < 1)
  filter_upwards [fragPerm_eventually_Ioo_half_one, fragPerm_third_delta_sq_le_one_sub_sq_eventually,
    fragPerm_third_delta_le_second_delta_eventually, hlocal, fragPerm_tail_bound_eventually] with
      r hr hδ3sq hδ3_le_old hloc hfar n θ hθδ3 hθπ
  by_cases hnear : |θ| ≤ fragPermSaddleDeltaReal r
  · have hbpos : 0 < fragPermSaddleBReal r := by
      unfold fragPermSaddleBReal
      have hrpos : 0 < r := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hr.1
      have hu_pos' : 0 < 1 - r := by linarith [hr.2]
      have hnum : 0 < r * (1 + r) := by positivity
      have hden : 0 < (1 - r) ^ 3 := pow_pos hu_pos' _
      exact div_pos hnum hden
    have hratio_close :
        ‖saddleLocalRatio fragPermFun fragPermSaddleAReal fragPermSaddleBReal r θ - 1‖ ≤ 1 :=
      hloc θ hnear
    have hratio_norm :
        ‖saddleLocalRatio fragPermFun fragPermSaddleAReal fragPermSaddleBReal r θ‖ ≤ 2 := by
      calc
        ‖saddleLocalRatio fragPermFun fragPermSaddleAReal fragPermSaddleBReal r θ‖
            = ‖(saddleLocalRatio fragPermFun fragPermSaddleAReal fragPermSaddleBReal r θ - 1) +
                1‖ := by ring_nf
        _ ≤ ‖saddleLocalRatio fragPermFun fragPermSaddleAReal fragPermSaddleBReal r θ - 1‖ +
              ‖(1 : ℂ)‖ := norm_add_le _ _
        _ ≤ 2 := by norm_num at hratio_close ⊢; linarith
    have hu_pos : 0 < 1 - r := by linarith [hr.2]
    have hu_nonneg : 0 ≤ 1 - r := hu_pos.le
    have hB_lower : (1 / 2 : ℝ) / (1 - r) ^ 3 ≤ fragPermSaddleBReal r := by
      unfold fragPermSaddleBReal
      have hden_pos : 0 < (1 - r) ^ 3 := by positivity
      have hnum_ge : (1 / 2 : ℝ) ≤ r * (1 + r) := by nlinarith [hr.1]
      exact div_le_div_of_nonneg_right hnum_ge hden_pos.le
    have hθsq : (fragPermThirdSaddleDeltaReal r) ^ 2 ≤ θ ^ 2 := by
      have hδ_nonneg : 0 ≤ fragPermThirdSaddleDeltaReal r := by
        unfold fragPermThirdSaddleDeltaReal
        exact Real.rpow_nonneg hu_nonneg _
      calc
        (fragPermThirdSaddleDeltaReal r) ^ 2 ≤ |θ| ^ 2 :=
          pow_le_pow_left₀ hδ_nonneg hθδ3 2
        _ = θ ^ 2 := by rw [sq_abs]
    have hscale_lower :
        (1 / 4 : ℝ) * (1 - r) ^ (-(1 / 10 : ℝ)) ≤
          fragPermSaddleBReal r * θ ^ 2 / 2 := by
      have hδsq_eq :
          (fragPermThirdSaddleDeltaReal r) ^ 2 =
            (1 - r) ^ (29 / 10 : ℝ) := by
        unfold fragPermThirdSaddleDeltaReal
        rw [← Real.rpow_mul_natCast hu_nonneg (29 / 20 : ℝ) 2]
        norm_num
      have hpow :
          ((1 / 2 : ℝ) / (1 - r) ^ 3) * (fragPermThirdSaddleDeltaReal r) ^ 2 / 2 =
            (1 / 4 : ℝ) * (1 - r) ^ (-(1 / 10 : ℝ)) := by
        rw [hδsq_eq]
        rw [show ((1 / 2 : ℝ) / (1 - r) ^ 3) *
              (1 - r) ^ (29 / 10 : ℝ) / 2 =
            (1 / 4 : ℝ) * (((1 - r) ^ 3)⁻¹ *
              (1 - r) ^ (29 / 10 : ℝ)) by ring]
        rw [show (1 - r) ^ 3 = (1 - r) ^ (3 : ℝ) by
          exact (Real.rpow_natCast (1 - r) 3).symm]
        rw [← Real.rpow_neg hu_nonneg (3 : ℝ)]
        rw [← Real.rpow_add hu_pos]
        norm_num
      calc
        (1 / 4 : ℝ) * (1 - r) ^ (-(1 / 10 : ℝ))
            = ((1 / 2 : ℝ) / (1 - r) ^ 3) *
                (fragPermThirdSaddleDeltaReal r) ^ 2 / 2 := hpow.symm
        _ ≤ fragPermSaddleBReal r * θ ^ 2 / 2 := by
          nlinarith [hB_lower, hθsq, hbpos.le, sq_nonneg θ]
    have hgauss :
        Real.exp (-(fragPermSaddleBReal r * θ ^ 2 / 2)) ≤
          Real.exp (-(1 / 4 : ℝ) * (1 - r) ^ (-(1 / 10 : ℝ))) := by
      exact Real.exp_le_exp.mpr (by linarith)
    have hnorm_eq :=
      saddleGAt_norm_eq_gaussian_mul_saddleLocalRatio_norm
        fragPermFun fragPermSaddleAReal fragPermSaddleBReal r n θ
    rw [hnorm_eq]
    unfold fragPermThirdTailE fragPermThirdNearTailE
    calc
      Real.exp (-(fragPermSaddleBReal r * θ ^ 2 / 2)) *
          ‖saddleLocalRatio fragPermFun fragPermSaddleAReal fragPermSaddleBReal r θ‖
          ≤ Real.exp (-(1 / 4 : ℝ) * (1 - r) ^ (-(1 / 10 : ℝ))) * 2 :=
            mul_le_mul hgauss hratio_norm (norm_nonneg _) (Real.exp_pos _).le
      _ ≤ 2 * Real.exp (-(1 / 4 : ℝ) * (1 - r) ^ (-(1 / 10 : ℝ))) +
            fragPermTailE r := by
            have hfar_nonneg : 0 ≤ fragPermTailE r := by
              unfold fragPermTailE
              positivity
            nlinarith
  · have hθold : fragPermSaddleDeltaReal r ≤ |θ| := le_of_not_ge hnear
    have hfar_bound := hfar n θ hθold hθπ
    unfold fragPermThirdTailE
    exact hfar_bound.trans (le_add_of_nonneg_left
      (by unfold fragPermThirdNearTailE; positivity))

lemma fragPerm_tail_third_uniform :
    ∃ E : ℝ → ℝ,
      (∀ᶠ r : ℝ in fragPermRadFilter, 0 ≤ E r) ∧
      Tendsto
        (fun r : ℝ => Real.sqrt (2 * Real.pi * fragPermSaddleBReal r) * E r /
          fragPermThirdCorrScale r)
        fragPermRadFilter (𝓝 0) ∧
      (∀ᶠ r : ℝ in fragPermRadFilter, ∀ n : ℕ, ∀ θ : ℝ,
        fragPermThirdSaddleDeltaReal r ≤ |θ| → |θ| ≤ Real.pi →
          ‖saddleGAt fragPermFun r n θ‖ ≤ E r) := by
  exact ⟨fragPermThirdTailE, fragPermThirdTailE_nonneg_eventually,
    fragPermThirdTailE_decay, fragPerm_third_tail_bound_eventually⟩

/--
Robust third-order scale accepted by the generic `ThirdOrderHAdmissible`
interface.  The true finite-radius third-order correction is on the smaller
scale `(1-r)^2`; this robust scale is used only to reuse the abstract wrapper.
-/
def fragPermThirdRobustCorrScale (r : ℝ) : ℝ :=
  fragPermSecondCorrScale r

private def fragPermThirdGaussianDom (x : ℝ) : ℝ :=
  Real.exp (-(x ^ 2) / 2) *
    (|x| ^ 5 + |x| ^ 6 + |x| ^ 7 + |x| ^ 8 +
      |x| ^ 9 + |x| ^ 10 + |x| ^ 12)

private lemma fragPermThirdGaussianDom_nonneg (x : ℝ) :
    0 ≤ fragPermThirdGaussianDom x := by
  unfold fragPermThirdGaussianDom
  positivity

private lemma fragPerm_third_gaussian_abs_monomial_integrable (k : ℕ) :
    Integrable (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * |x| ^ k) := by
  have hk : (-1 : ℝ) < (k : ℝ) := by
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Nat.zero_le k)
    linarith
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

private lemma fragPermThirdGaussianDom_integrable : Integrable fragPermThirdGaussianDom := by
  let g : ℕ → ℝ → ℝ := fun k x => Real.exp (-(x ^ 2) / 2) * |x| ^ k
  have hsum :
      Integrable (fun x : ℝ =>
        g 5 x + g 6 x + g 7 x + g 8 x + g 9 x + g 10 x + g 12 x) := by
    simpa [g, add_assoc] using
      ((((((fragPerm_third_gaussian_abs_monomial_integrable 5).add
        (fragPerm_third_gaussian_abs_monomial_integrable 6)).add
        (fragPerm_third_gaussian_abs_monomial_integrable 7)).add
        (fragPerm_third_gaussian_abs_monomial_integrable 8)).add
        (fragPerm_third_gaussian_abs_monomial_integrable 9)).add
        (fragPerm_third_gaussian_abs_monomial_integrable 10)).add
        (fragPerm_third_gaussian_abs_monomial_integrable 12)
  convert hsum using 1
  ext x
  unfold fragPermThirdGaussianDom
  dsimp [g]
  ring_nf

private lemma fragPermThirdGaussianDom_integral_nonneg :
    0 ≤ ∫ x : ℝ, fragPermThirdGaussianDom x :=
  integral_nonneg (fun x => fragPermThirdGaussianDom_nonneg x)

private lemma fragPermThirdGaussianDom_continuous : Continuous fragPermThirdGaussianDom := by
  unfold fragPermThirdGaussianDom
  fun_prop

private lemma fragPermThirdGaussianDom_window_le_integral {L : ℝ} (hL : 0 ≤ L) :
    (∫ x in -L..L, fragPermThirdGaussianDom x) ≤ ∫ x : ℝ, fragPermThirdGaussianDom x := by
  have hle : -L ≤ L := by linarith
  rw [intervalIntegral.integral_of_le hle]
  exact setIntegral_le_integral fragPermThirdGaussianDom_integrable
    (Eventually.of_forall fragPermThirdGaussianDom_nonneg)

/-- A larger local domination function for the finite-radius third-order
Taylor remainder. -/
private def fragPermThirdLocalDom (x : ℝ) : ℝ :=
  Real.exp (-(x ^ 2) / 2) * ∑ k ∈ Finset.range 36, |x| ^ k

private lemma fragPermThirdLocalDom_nonneg (x : ℝ) :
    0 ≤ fragPermThirdLocalDom x := by
  unfold fragPermThirdLocalDom
  positivity

private lemma fragPermThirdLocalDom_integrable : Integrable fragPermThirdLocalDom := by
  have hterms :
      ∀ k ∈ Finset.range 36,
        Integrable (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * |x| ^ k) := by
    intro k hk
    exact fragPerm_third_gaussian_abs_monomial_integrable k
  have hsum :
      Integrable
        (fun x : ℝ =>
          ∑ k ∈ Finset.range 36, Real.exp (-(x ^ 2) / 2) * |x| ^ k) :=
    integrable_finset_sum (Finset.range 36) hterms
  convert hsum using 1
  ext x
  unfold fragPermThirdLocalDom
  rw [Finset.mul_sum]

private lemma fragPermThirdLocalDom_integral_nonneg :
    0 ≤ ∫ x : ℝ, fragPermThirdLocalDom x :=
  integral_nonneg (fun x => fragPermThirdLocalDom_nonneg x)

private lemma fragPermThirdLocalDom_continuous : Continuous fragPermThirdLocalDom := by
  unfold fragPermThirdLocalDom
  fun_prop

private lemma fragPermThirdLocalDom_window_le_integral {L : ℝ} (hL : 0 ≤ L) :
    (∫ x in -L..L, fragPermThirdLocalDom x) ≤ ∫ x : ℝ, fragPermThirdLocalDom x := by
  have hle : -L ≤ L := by linarith
  rw [intervalIntegral.integral_of_le hle]
  exact setIntegral_le_integral fragPermThirdLocalDom_integrable
    (Eventually.of_forall fragPermThirdLocalDom_nonneg)

private def fragPermThirdScaledCubic (r x : ℝ) : ℂ :=
  -Complex.I *
    ((fragPermSaddleB3Real r : ℂ) /
      (6 * (Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 3)) * (x : ℂ) ^ 3

private def fragPermThirdScaledQuartic (r x : ℝ) : ℂ :=
  ((fragPermSaddleB4Real r : ℂ) / (24 * (fragPermSaddleBReal r : ℂ) ^ 2)) *
    (x : ℂ) ^ 4

private def fragPermThirdScaledFifth (r x : ℝ) : ℂ :=
  Complex.I *
    ((fragPermSaddleB5Real r : ℂ) /
      (120 * (Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 5)) * (x : ℂ) ^ 5

private def fragPermThirdScaledSixth (r x : ℝ) : ℂ :=
  -((fragPermSaddleB6Real r : ℂ) / (720 * (fragPermSaddleBReal r : ℂ) ^ 3)) *
    (x : ℂ) ^ 6

private def fragPermThirdScaledRemainder (r x : ℝ) : ℂ :=
  fragPermLocalExponent r (x / Real.sqrt (fragPermSaddleBReal r)) -
    fragPermThirdScaledCubic r x - fragPermThirdScaledQuartic r x -
      fragPermThirdScaledFifth r x - fragPermThirdScaledSixth r x

private lemma fragPermThirdLocalExponent_scaled_split (r x : ℝ) :
    fragPermLocalExponent r (x / Real.sqrt (fragPermSaddleBReal r)) =
      fragPermThirdScaledCubic r x + fragPermThirdScaledQuartic r x +
        fragPermThirdScaledFifth r x + fragPermThirdScaledSixth r x +
          fragPermThirdScaledRemainder r x := by
  unfold fragPermThirdScaledRemainder
  ring

private lemma fragPermSaddleBReal_lower_half {r : ℝ}
    (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1) :
    (1 / 2 : ℝ) / (1 - r) ^ 3 ≤ fragPermSaddleBReal r := by
  unfold fragPermSaddleBReal
  have hu_pos : 0 < 1 - r := by linarith [hr.2]
  have hden_pos : 0 < (1 - r) ^ 3 := by positivity
  have hnum_ge : (1 / 2 : ℝ) ≤ r * (1 + r) := by nlinarith [hr.1]
  exact div_le_div_of_nonneg_right hnum_ge hden_pos.le

private lemma fragPermSaddleBReal_inv_le {r : ℝ}
    (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1) :
    (fragPermSaddleBReal r)⁻¹ ≤ 2 * (1 - r) ^ 3 := by
  have hu_pos : 0 < 1 - r := by linarith [hr.2]
  have hB_lower := fragPermSaddleBReal_lower_half hr
  have hlow_pos : 0 < (1 / 2 : ℝ) / (1 - r) ^ 3 := by positivity
  have h := inv_anti₀ hlow_pos hB_lower
  calc
    (fragPermSaddleBReal r)⁻¹ ≤ ((1 / 2 : ℝ) / (1 - r) ^ 3)⁻¹ := h
    _ = 2 * (1 - r) ^ 3 := by field_simp [hu_pos.ne']

private lemma fragPermSaddleB3Real_le {r : ℝ}
    (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1) :
    fragPermSaddleB3Real r ≤ 6 / (1 - r) ^ 4 := by
  unfold fragPermSaddleB3Real
  have hrpos : 0 < r := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hr.1
  have hrle : r ≤ 1 := hr.2.le
  have hu_pos : 0 < 1 - r := by linarith [hr.2]
  have hden_pos : 0 < (1 - r) ^ 4 := pow_pos hu_pos _
  have hpoly : 1 + 4 * r + r ^ 2 ≤ 6 := by
    nlinarith [hr.1, hrle, sq_nonneg r, sq_nonneg (1 - r)]
  have hpoly_nonneg : 0 ≤ 1 + 4 * r + r ^ 2 := by positivity
  calc
    r * (1 + 4 * r + r ^ 2) / (1 - r) ^ 4
        ≤ 1 * 6 / (1 - r) ^ 4 := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul hrle hpoly hpoly_nonneg zero_le_one) hden_pos.le
    _ = 6 / (1 - r) ^ 4 := by ring

private lemma fragPermSaddleB4Real_le {r : ℝ}
    (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1) :
    fragPermSaddleB4Real r ≤ 24 / (1 - r) ^ 5 := by
  unfold fragPermSaddleB4Real
  have hrpos : 0 < r := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hr.1
  have hrle : r ≤ 1 := hr.2.le
  have hu_pos : 0 < 1 - r := by linarith [hr.2]
  have hden_pos : 0 < (1 - r) ^ 5 := pow_pos hu_pos _
  have hpoly : 1 + 11 * r + 11 * r ^ 2 + r ^ 3 ≤ 24 := by
    nlinarith [hr.1, hrle, sq_nonneg r, sq_nonneg (1 - r), sq_nonneg (r - 1)]
  have hpoly_nonneg : 0 ≤ 1 + 11 * r + 11 * r ^ 2 + r ^ 3 := by positivity
  calc
    r * (1 + 11 * r + 11 * r ^ 2 + r ^ 3) / (1 - r) ^ 5
        ≤ 1 * 24 / (1 - r) ^ 5 := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul hrle hpoly hpoly_nonneg zero_le_one) hden_pos.le
    _ = 24 / (1 - r) ^ 5 := by ring

private lemma fragPermSaddleB5Real_le {r : ℝ}
    (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1) :
    fragPermSaddleB5Real r ≤ 120 / (1 - r) ^ 6 := by
  unfold fragPermSaddleB5Real
  have hrpos : 0 < r := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hr.1
  have hrle : r ≤ 1 := hr.2.le
  have hu_pos : 0 < 1 - r := by linarith [hr.2]
  have hden_pos : 0 < (1 - r) ^ 6 := pow_pos hu_pos _
  have hpoly :
      1 + 26 * r + 66 * r ^ 2 + 26 * r ^ 3 + r ^ 4 ≤ 120 := by
    nlinarith [hr.1, hrle, sq_nonneg r, sq_nonneg (1 - r), sq_nonneg (r - 1),
      show 0 ≤ r ^ 3 by positivity, show 0 ≤ r ^ 4 by positivity]
  have hpoly_nonneg : 0 ≤ 1 + 26 * r + 66 * r ^ 2 + 26 * r ^ 3 + r ^ 4 := by
    positivity
  calc
    r * (1 + 26 * r + 66 * r ^ 2 + 26 * r ^ 3 + r ^ 4) / (1 - r) ^ 6
        ≤ 1 * 120 / (1 - r) ^ 6 := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul hrle hpoly hpoly_nonneg zero_le_one) hden_pos.le
    _ = 120 / (1 - r) ^ 6 := by ring

private lemma fragPermSaddleB6Real_le {r : ℝ}
    (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1) :
    fragPermSaddleB6Real r ≤ 720 / (1 - r) ^ 7 := by
  unfold fragPermSaddleB6Real
  have hrpos : 0 < r := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hr.1
  have hrle : r ≤ 1 := hr.2.le
  have hu_pos : 0 < 1 - r := by linarith [hr.2]
  have hden_pos : 0 < (1 - r) ^ 7 := pow_pos hu_pos _
  have hpoly :
      1 + 56 * r + 246 * r ^ 2 + 56 * r ^ 3 + r ^ 4 ≤ 360 := by
    nlinarith [hr.1, hrle, sq_nonneg r, sq_nonneg (1 - r), sq_nonneg (r - 1),
      show 0 ≤ r ^ 3 by positivity, show 0 ≤ r ^ 4 by positivity]
  have hpoly_nonneg :
      0 ≤ 1 + 56 * r + 246 * r ^ 2 + 56 * r ^ 3 + r ^ 4 := by
    positivity
  have hnum : r * (1 + r) *
      (1 + 56 * r + 246 * r ^ 2 + 56 * r ^ 3 + r ^ 4) ≤ 720 := by
    have hr1 : r * (1 + r) ≤ 2 := by nlinarith [hr.1, hrle]
    have hfactor_nonneg : 0 ≤ r * (1 + r) := by positivity
    calc
      r * (1 + r) *
          (1 + 56 * r + 246 * r ^ 2 + 56 * r ^ 3 + r ^ 4)
          ≤ 2 * 360 := by
            exact mul_le_mul hr1 hpoly hpoly_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      _ = 720 := by norm_num
  calc
    r * (1 + r) * (1 + 56 * r + 246 * r ^ 2 + 56 * r ^ 3 + r ^ 4) /
        (1 - r) ^ 7
        ≤ 720 / (1 - r) ^ 7 := div_le_div_of_nonneg_right hnum hden_pos.le

private lemma fragPermSqrtB_inv_le {r : ℝ}
    (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1) :
    (Real.sqrt (fragPermSaddleBReal r))⁻¹ ≤
      2 * (1 - r) ^ (3 / 2 : ℝ) := by
  have hu_pos : 0 < 1 - r := by linarith [hr.2]
  have hu_nonneg : 0 ≤ 1 - r := hu_pos.le
  have hlow := fragPerm_sqrt_b_lower_of_Ioo_half_one hr
  have hlow_pos :
      0 < (1 / 2 : ℝ) * (1 - r) ^ (-(3 / 2 : ℝ)) := by
    positivity
  have h := inv_anti₀ hlow_pos hlow
  calc
    (Real.sqrt (fragPermSaddleBReal r))⁻¹
        ≤ ((1 / 2 : ℝ) * (1 - r) ^ (-(3 / 2 : ℝ)))⁻¹ := h
    _ = 2 * (1 - r) ^ (3 / 2 : ℝ) := by
      have hp : 0 < (1 - r) ^ (-(3 / 2 : ℝ)) :=
        Real.rpow_pos_of_pos hu_pos _
      field_simp [hp.ne']
      rw [← Real.rpow_add hu_pos]
      norm_num

private lemma fragPerm_rpow_calc_half {u : ℝ} (hu : 0 < u) :
    (1 / u ^ 4) * (2 * u ^ (3 / 2 : ℝ)) ^ 3 =
      8 * u ^ (1 / 2 : ℝ) := by
  have hun : 0 ≤ u := hu.le
  have hpow :
      (u ^ (3 / 2 : ℝ)) ^ 3 = u ^ (9 / 2 : ℝ) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hun]
    norm_num
  calc
    (1 / u ^ 4) * (2 * u ^ (3 / 2 : ℝ)) ^ 3
        = 8 * (u ^ (9 / 2 : ℝ) / u ^ 4) := by
          rw [mul_pow, hpow]
          ring
    _ = 8 * u ^ (1 / 2 : ℝ) := by
      rw [show u ^ 4 = u ^ (4 : ℝ) by exact (Real.rpow_natCast u 4).symm]
      rw [div_eq_mul_inv]
      rw [← Real.rpow_neg hun (4 : ℝ)]
      rw [← Real.rpow_add hu]
      norm_num

private lemma fragPerm_rpow_calc_one {u : ℝ} (hu : 0 < u) :
    (1 / u ^ 5) * (2 * u ^ 3) ^ 2 = 4 * u := by
  field_simp [hu.ne']
  ring

private lemma fragPerm_rpow_calc_three_halves {u : ℝ} (hu : 0 < u) :
    (1 / u ^ 6) * (2 * u ^ (3 / 2 : ℝ)) ^ 5 =
      32 * u ^ (3 / 2 : ℝ) := by
  have hun : 0 ≤ u := hu.le
  have hpow :
      (u ^ (3 / 2 : ℝ)) ^ 5 = u ^ (15 / 2 : ℝ) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hun]
    norm_num
  calc
    (1 / u ^ 6) * (2 * u ^ (3 / 2 : ℝ)) ^ 5
        = 32 * (u ^ (15 / 2 : ℝ) / u ^ 6) := by
          rw [mul_pow, hpow]
          ring
    _ = 32 * u ^ (3 / 2 : ℝ) := by
      rw [show u ^ 6 = u ^ (6 : ℝ) by exact (Real.rpow_natCast u 6).symm]
      rw [div_eq_mul_inv]
      rw [← Real.rpow_neg hun (6 : ℝ)]
      rw [← Real.rpow_add hu]
      norm_num

private lemma fragPerm_rpow_calc_two {u : ℝ} (hu : 0 < u) :
    (1 / u ^ 7) * (2 * u ^ 3) ^ 3 = 8 * u ^ 2 := by
  field_simp [hu.ne']
  ring

private lemma fragPermThirdScaledCubic_norm_le {r x : ℝ}
    (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1) :
    ‖fragPermThirdScaledCubic r x‖ ≤
      10 * (1 - r) ^ (1 / 2 : ℝ) * |x| ^ 3 := by
  let u : ℝ := 1 - r
  have hrpos : 0 < r := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hr.1
  have hu_pos : 0 < u := by dsimp [u]; linarith [hr.2]
  have hu_nonneg : 0 ≤ u := hu_pos.le
  have hbpos : 0 < fragPermSaddleBReal r := by
    unfold fragPermSaddleBReal
    have hrpos : 0 < r := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hr.1
    have hnum : 0 < r * (1 + r) := by positivity
    have hden : 0 < (1 - r) ^ 3 := by positivity
    exact div_pos hnum hden
  have hsqrt_pos : 0 < Real.sqrt (fragPermSaddleBReal r) := Real.sqrt_pos.mpr hbpos
  have hb3_nonneg : 0 ≤ fragPermSaddleB3Real r := by
    unfold fragPermSaddleB3Real
    positivity
  have hb3_div : fragPermSaddleB3Real r / 6 ≤ 1 / u ^ 4 := by
    have h : fragPermSaddleB3Real r ≤ 6 / u ^ 4 := by
      simpa [u] using fragPermSaddleB3Real_le hr
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 6)]
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
  have hinv := fragPermSqrtB_inv_le hr
  have hinv3 :
      (Real.sqrt (fragPermSaddleBReal r))⁻¹ ^ 3 ≤
        (2 * u ^ (3 / 2 : ℝ)) ^ 3 := by
    dsimp [u] at hinv
    exact pow_le_pow_left₀ (inv_nonneg.mpr (Real.sqrt_nonneg _)) hinv 3
  have hcoef :
      ‖(fragPermSaddleB3Real r : ℂ) /
          (6 * (Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 3)‖ ≤
        10 * u ^ (1 / 2 : ℝ) := by
    calc
      ‖(fragPermSaddleB3Real r : ℂ) /
          (6 * (Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 3)‖
          = (fragPermSaddleB3Real r / 6) *
              (Real.sqrt (fragPermSaddleBReal r))⁻¹ ^ 3 := by
            rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg hb3_nonneg]
            simp only [norm_mul, norm_ofNat, norm_pow, Complex.norm_real, Real.norm_eq_abs]
            rw [abs_of_pos hsqrt_pos]
            field_simp [hsqrt_pos.ne']
      _ ≤ (1 / u ^ 4) * (2 * u ^ (3 / 2 : ℝ)) ^ 3 := by
            exact mul_le_mul hb3_div hinv3
              (pow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) 3)
              (div_nonneg (by norm_num) (pow_nonneg hu_nonneg 4))
      _ = 8 * u ^ (1 / 2 : ℝ) := fragPerm_rpow_calc_half hu_pos
      _ ≤ 10 * u ^ (1 / 2 : ℝ) := by
        have hpow : 0 ≤ u ^ (1 / 2 : ℝ) := Real.rpow_nonneg hu_nonneg _
        nlinarith
  calc
    ‖fragPermThirdScaledCubic r x‖
        = ‖(fragPermSaddleB3Real r : ℂ) /
            (6 * (Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 3)‖ * |x| ^ 3 := by
          unfold fragPermThirdScaledCubic
          rw [norm_mul, norm_mul, norm_neg, norm_I, one_mul, norm_pow,
            Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (10 * u ^ (1 / 2 : ℝ)) * |x| ^ 3 :=
      mul_le_mul_of_nonneg_right hcoef (pow_nonneg (abs_nonneg x) 3)
    _ = 10 * (1 - r) ^ (1 / 2 : ℝ) * |x| ^ 3 := by dsimp [u]

private lemma fragPermThirdScaledQuartic_norm_le {r x : ℝ}
    (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1) :
    ‖fragPermThirdScaledQuartic r x‖ ≤ 10 * (1 - r) * |x| ^ 4 := by
  let u : ℝ := 1 - r
  have hrpos : 0 < r := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hr.1
  have hu_pos : 0 < u := by dsimp [u]; linarith [hr.2]
  have hu_nonneg : 0 ≤ u := hu_pos.le
  have hbpos : 0 < fragPermSaddleBReal r := by
    unfold fragPermSaddleBReal
    have hrpos : 0 < r := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hr.1
    have hnum : 0 < r * (1 + r) := by positivity
    have hden : 0 < (1 - r) ^ 3 := by positivity
    exact div_pos hnum hden
  have hb4_nonneg : 0 ≤ fragPermSaddleB4Real r := by
    unfold fragPermSaddleB4Real
    positivity
  have hb4_div : fragPermSaddleB4Real r / 24 ≤ 1 / u ^ 5 := by
    have h : fragPermSaddleB4Real r ≤ 24 / u ^ 5 := by
      simpa [u] using fragPermSaddleB4Real_le hr
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 24)]
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
  have hinv := fragPermSaddleBReal_inv_le hr
  have hinv2 :
      (fragPermSaddleBReal r)⁻¹ ^ 2 ≤ (2 * u ^ 3) ^ 2 := by
    dsimp [u] at hinv
    exact pow_le_pow_left₀ (inv_nonneg.mpr hbpos.le) hinv 2
  have hcoef :
      ‖(fragPermSaddleB4Real r : ℂ) /
          (24 * (fragPermSaddleBReal r : ℂ) ^ 2)‖ ≤ 10 * u := by
    calc
      ‖(fragPermSaddleB4Real r : ℂ) /
          (24 * (fragPermSaddleBReal r : ℂ) ^ 2)‖
          = (fragPermSaddleB4Real r / 24) * (fragPermSaddleBReal r)⁻¹ ^ 2 := by
            rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg hb4_nonneg]
            simp only [norm_mul, norm_ofNat, norm_pow, Complex.norm_real, Real.norm_eq_abs]
            rw [abs_of_pos hbpos]
            field_simp [hbpos.ne']
      _ ≤ (1 / u ^ 5) * (2 * u ^ 3) ^ 2 := by
            exact mul_le_mul hb4_div hinv2
              (pow_nonneg (inv_nonneg.mpr hbpos.le) 2)
              (div_nonneg (by norm_num) (pow_nonneg hu_nonneg 5))
      _ = 4 * u := fragPerm_rpow_calc_one hu_pos
      _ ≤ 10 * u := by nlinarith [hu_pos]
  calc
    ‖fragPermThirdScaledQuartic r x‖
        = ‖(fragPermSaddleB4Real r : ℂ) /
            (24 * (fragPermSaddleBReal r : ℂ) ^ 2)‖ * |x| ^ 4 := by
          unfold fragPermThirdScaledQuartic
          rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (10 * u) * |x| ^ 4 :=
      mul_le_mul_of_nonneg_right hcoef (pow_nonneg (abs_nonneg x) 4)
    _ = 10 * (1 - r) * |x| ^ 4 := by dsimp [u]

private lemma fragPermThirdScaledFifth_norm_le {r x : ℝ}
    (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1) :
    ‖fragPermThirdScaledFifth r x‖ ≤
      40 * (1 - r) ^ (3 / 2 : ℝ) * |x| ^ 5 := by
  let u : ℝ := 1 - r
  have hrpos : 0 < r := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hr.1
  have hu_pos : 0 < u := by dsimp [u]; linarith [hr.2]
  have hu_nonneg : 0 ≤ u := hu_pos.le
  have hbpos : 0 < fragPermSaddleBReal r := by
    unfold fragPermSaddleBReal
    dsimp [u] at hu_pos
    positivity
  have hsqrt_pos : 0 < Real.sqrt (fragPermSaddleBReal r) := Real.sqrt_pos.mpr hbpos
  have hb5_nonneg : 0 ≤ fragPermSaddleB5Real r :=
    fragPermSaddleB5Real_nonneg_of_Ioo_zero_one
      ⟨lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hr.1, hr.2⟩
  have hb5_div : fragPermSaddleB5Real r / 120 ≤ 1 / u ^ 6 := by
    have h : fragPermSaddleB5Real r ≤ 120 / u ^ 6 := by
      simpa [u] using fragPermSaddleB5Real_le hr
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 120)]
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
  have hinv := fragPermSqrtB_inv_le hr
  have hinv5 :
      (Real.sqrt (fragPermSaddleBReal r))⁻¹ ^ 5 ≤
        (2 * u ^ (3 / 2 : ℝ)) ^ 5 := by
    dsimp [u] at hinv
    exact pow_le_pow_left₀ (inv_nonneg.mpr (Real.sqrt_nonneg _)) hinv 5
  have hcoef :
      ‖(fragPermSaddleB5Real r : ℂ) /
          (120 * (Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 5)‖ ≤
        40 * u ^ (3 / 2 : ℝ) := by
    calc
      ‖(fragPermSaddleB5Real r : ℂ) /
          (120 * (Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 5)‖
          = (fragPermSaddleB5Real r / 120) *
              (Real.sqrt (fragPermSaddleBReal r))⁻¹ ^ 5 := by
            rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg hb5_nonneg]
            simp only [norm_mul, norm_ofNat, norm_pow, Complex.norm_real, Real.norm_eq_abs]
            rw [abs_of_pos hsqrt_pos]
            field_simp [hsqrt_pos.ne']
      _ ≤ (1 / u ^ 6) * (2 * u ^ (3 / 2 : ℝ)) ^ 5 := by
            exact mul_le_mul hb5_div hinv5
              (pow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) 5)
              (div_nonneg (by norm_num) (pow_nonneg hu_nonneg 6))
      _ = 32 * u ^ (3 / 2 : ℝ) := fragPerm_rpow_calc_three_halves hu_pos
      _ ≤ 40 * u ^ (3 / 2 : ℝ) := by
        have hpow : 0 ≤ u ^ (3 / 2 : ℝ) := Real.rpow_nonneg hu_nonneg _
        nlinarith
  calc
    ‖fragPermThirdScaledFifth r x‖
        = ‖(fragPermSaddleB5Real r : ℂ) /
            (120 * (Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 5)‖ * |x| ^ 5 := by
          unfold fragPermThirdScaledFifth
          rw [norm_mul, norm_mul, norm_I, one_mul, norm_pow,
            Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (40 * u ^ (3 / 2 : ℝ)) * |x| ^ 5 :=
      mul_le_mul_of_nonneg_right hcoef (pow_nonneg (abs_nonneg x) 5)
    _ = 40 * (1 - r) ^ (3 / 2 : ℝ) * |x| ^ 5 := by dsimp [u]

private lemma fragPermThirdScaledSixth_norm_le {r x : ℝ}
    (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1) :
    ‖fragPermThirdScaledSixth r x‖ ≤ 10 * (1 - r) ^ 2 * |x| ^ 6 := by
  let u : ℝ := 1 - r
  have hrpos : 0 < r := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hr.1
  have hu_pos : 0 < u := by dsimp [u]; linarith [hr.2]
  have hu_nonneg : 0 ≤ u := hu_pos.le
  have hbpos : 0 < fragPermSaddleBReal r := by
    unfold fragPermSaddleBReal
    dsimp [u] at hu_pos
    positivity
  have hb6_nonneg : 0 ≤ fragPermSaddleB6Real r :=
    fragPermSaddleB6Real_nonneg_of_Ioo_zero_one
      ⟨lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hr.1, hr.2⟩
  have hb6_div : fragPermSaddleB6Real r / 720 ≤ 1 / u ^ 7 := by
    have h : fragPermSaddleB6Real r ≤ 720 / u ^ 7 := by
      simpa [u] using fragPermSaddleB6Real_le hr
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 720)]
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
  have hinv := fragPermSaddleBReal_inv_le hr
  have hinv3 :
      (fragPermSaddleBReal r)⁻¹ ^ 3 ≤ (2 * u ^ 3) ^ 3 := by
    dsimp [u] at hinv
    exact pow_le_pow_left₀ (inv_nonneg.mpr hbpos.le) hinv 3
  have hcoef :
      ‖(fragPermSaddleB6Real r : ℂ) /
          (720 * (fragPermSaddleBReal r : ℂ) ^ 3)‖ ≤ 10 * u ^ 2 := by
    calc
      ‖(fragPermSaddleB6Real r : ℂ) /
          (720 * (fragPermSaddleBReal r : ℂ) ^ 3)‖
          = (fragPermSaddleB6Real r / 720) * (fragPermSaddleBReal r)⁻¹ ^ 3 := by
            rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg hb6_nonneg]
            simp only [norm_mul, norm_ofNat, norm_pow, Complex.norm_real, Real.norm_eq_abs]
            rw [abs_of_pos hbpos]
            field_simp [hbpos.ne']
      _ ≤ (1 / u ^ 7) * (2 * u ^ 3) ^ 3 := by
            exact mul_le_mul hb6_div hinv3
              (pow_nonneg (inv_nonneg.mpr hbpos.le) 3)
              (div_nonneg (by norm_num) (pow_nonneg hu_nonneg 7))
      _ = 8 * u ^ 2 := fragPerm_rpow_calc_two hu_pos
      _ ≤ 10 * u ^ 2 := by nlinarith [sq_nonneg u]
  calc
    ‖fragPermThirdScaledSixth r x‖
        = ‖(fragPermSaddleB6Real r : ℂ) /
            (720 * (fragPermSaddleBReal r : ℂ) ^ 3)‖ * |x| ^ 6 := by
          unfold fragPermThirdScaledSixth
          rw [norm_mul, norm_neg, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (10 * u ^ 2) * |x| ^ 6 :=
      mul_le_mul_of_nonneg_right hcoef (pow_nonneg (abs_nonneg x) 6)
    _ = 10 * (1 - r) ^ 2 * |x| ^ 6 := by dsimp [u]

private lemma fragPermThird_sqrtB_sq {r : ℝ} (hb : 0 < fragPermSaddleBReal r) :
    ((Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 2) =
      (fragPermSaddleBReal r : ℂ) := by
  exact_mod_cast (Real.sq_sqrt hb.le)

private lemma fragPerm_saddleThirdPoly_eq_scaled_terms {r x : ℝ}
    (hb : 0 < fragPermSaddleBReal r) :
    saddleThirdPoly fragPermSaddleBReal fragPermSaddleB3Real fragPermSaddleB4Real
        fragPermSaddleB5Real fragPermSaddleB6Real r x =
      1 + fragPermThirdScaledCubic r x + fragPermThirdScaledQuartic r x +
        (fragPermThirdScaledCubic r x) ^ 2 / 2 +
        fragPermThirdScaledFifth r x + fragPermThirdScaledSixth r x +
        fragPermThirdScaledCubic r x * fragPermThirdScaledQuartic r x +
        fragPermThirdScaledCubic r x * fragPermThirdScaledFifth r x +
        (fragPermThirdScaledQuartic r x) ^ 2 / 2 +
        (fragPermThirdScaledCubic r x) ^ 3 / 6 +
        (fragPermThirdScaledCubic r x) ^ 2 * fragPermThirdScaledQuartic r x / 2 +
        (fragPermThirdScaledCubic r x) ^ 4 / 24 := by
  have hsqrt_sq := fragPermThird_sqrtB_sq hb
  have hsqrt_ne : (Real.sqrt (fragPermSaddleBReal r) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hb).ne'
  have hb_ne : (fragPermSaddleBReal r : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hb.ne'
  have hsqrt_pow6 :
      (Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 6 =
        (fragPermSaddleBReal r : ℂ) ^ 3 := by
    calc
      (Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 6 =
          ((Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 2) ^ 3 := by ring
      _ = (fragPermSaddleBReal r : ℂ) ^ 3 := by rw [hsqrt_sq]
  have hsqrt_pow8 :
      (Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 8 =
        (fragPermSaddleBReal r : ℂ) ^ 4 := by
    calc
      (Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 8 =
          ((Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 2) ^ 4 := by ring
      _ = (fragPermSaddleBReal r : ℂ) ^ 4 := by rw [hsqrt_sq]
  have hsqrt_pow12 :
      (Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 12 =
        (fragPermSaddleBReal r : ℂ) ^ 6 := by
    calc
      (Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 12 =
          ((Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 2) ^ 6 := by ring
      _ = (fragPermSaddleBReal r : ℂ) ^ 6 := by rw [hsqrt_sq]
  unfold saddleThirdPoly saddleSecondPoly fragPermThirdScaledCubic
    fragPermThirdScaledQuartic fragPermThirdScaledFifth fragPermThirdScaledSixth
  rw [← hsqrt_sq]
  field_simp [hsqrt_ne]
  ring_nf
  simp [Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four, Complex.ofReal_pow]
  ring

private lemma fragPermThirdScaledRemainder_eq_unscaled {r x : ℝ}
    (hb : 0 < fragPermSaddleBReal r) :
    fragPermThirdScaledRemainder r x =
      fragPermLocalExponent r (x / Real.sqrt (fragPermSaddleBReal r)) -
        (-Complex.I * ((fragPermSaddleB3Real r : ℂ) / 6) *
            ((x / Real.sqrt (fragPermSaddleBReal r) : ℝ) : ℂ) ^ 3 +
          ((fragPermSaddleB4Real r : ℂ) / 24) *
            ((x / Real.sqrt (fragPermSaddleBReal r) : ℝ) : ℂ) ^ 4 +
          Complex.I * ((fragPermSaddleB5Real r : ℂ) / 120) *
            ((x / Real.sqrt (fragPermSaddleBReal r) : ℝ) : ℂ) ^ 5 -
          ((fragPermSaddleB6Real r : ℂ) / 720) *
            ((x / Real.sqrt (fragPermSaddleBReal r) : ℝ) : ℂ) ^ 6) := by
  have hsqrt_ne : (Real.sqrt (fragPermSaddleBReal r) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hb).ne'
  have hb_ne : (fragPermSaddleBReal r : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hb.ne'
  have hsqrt_sq := fragPermThird_sqrtB_sq hb
  have hsqrt_pow4 :
      (Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 4 =
        (fragPermSaddleBReal r : ℂ) ^ 2 := by
    calc
      (Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 4 =
          ((Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 2) ^ 2 := by ring
      _ = (fragPermSaddleBReal r : ℂ) ^ 2 := by rw [hsqrt_sq]
  have hsqrt_pow6 :
      (Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 6 =
        (fragPermSaddleBReal r : ℂ) ^ 3 := by
    calc
      (Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 6 =
          ((Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 2) ^ 3 := by ring
      _ = (fragPermSaddleBReal r : ℂ) ^ 3 := by rw [hsqrt_sq]
  have hθ3 :
      ((x / Real.sqrt (fragPermSaddleBReal r) : ℝ) : ℂ) ^ 3 =
        (x : ℂ) ^ 3 / (Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 3 := by
    norm_num [Complex.ofReal_div]
    ring
  have hθ4 :
      ((x / Real.sqrt (fragPermSaddleBReal r) : ℝ) : ℂ) ^ 4 =
        (x : ℂ) ^ 4 / (Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 4 := by
    norm_num [Complex.ofReal_div]
    ring
  have hθ5 :
      ((x / Real.sqrt (fragPermSaddleBReal r) : ℝ) : ℂ) ^ 5 =
        (x : ℂ) ^ 5 / (Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 5 := by
    norm_num [Complex.ofReal_div]
    ring
  have hθ6 :
      ((x / Real.sqrt (fragPermSaddleBReal r) : ℝ) : ℂ) ^ 6 =
        (x : ℂ) ^ 6 / (Real.sqrt (fragPermSaddleBReal r) : ℂ) ^ 6 := by
    norm_num [Complex.ofReal_div]
    ring
  unfold fragPermThirdScaledRemainder fragPermThirdScaledCubic
    fragPermThirdScaledQuartic fragPermThirdScaledFifth fragPermThirdScaledSixth
  rw [hθ3, hθ4, hθ5, hθ6, hsqrt_pow4, hsqrt_pow6]
  field_simp [hsqrt_ne, hb_ne]
  ring

private lemma complex_exp_third_error_bound (C Q F S R W : ℂ)
    (hW : W = C + Q + F + S + R) (hWnorm : ‖W‖ ≤ 1) :
    ‖Complex.exp W -
      (1 + C + Q + C ^ 2 / 2 + F + S + C * Q + C * F + Q ^ 2 / 2 +
        C ^ 3 / 6 + C ^ 2 * Q / 2 + C ^ 4 / 24)‖ ≤
      Real.exp 1 * ‖W‖ ^ 5 + ‖R‖ +
        ‖W ^ 2 - (C ^ 2 + 2 * C * Q + 2 * C * F + Q ^ 2)‖ +
        ‖W ^ 3 - (C ^ 3 + 3 * C ^ 2 * Q)‖ +
        ‖W ^ 4 - C ^ 4‖ := by
  have hsum :
      (∑ m ∈ Finset.range 5, W ^ m / (m.factorial : ℂ)) =
        1 + W + W ^ 2 / 2 + W ^ 3 / 6 + W ^ 4 / 24 := by
    norm_num [Finset.sum_range_succ]
  have htail :
      ‖Complex.exp W - (1 + W + W ^ 2 / 2 + W ^ 3 / 6 + W ^ 4 / 24)‖ ≤
        Real.exp 1 * ‖W‖ ^ 5 := by
    calc
      ‖Complex.exp W - (1 + W + W ^ 2 / 2 + W ^ 3 / 6 + W ^ 4 / 24)‖ =
          ‖Complex.exp W - ∑ m ∈ Finset.range 5, W ^ m / (m.factorial : ℂ)‖ := by
            rw [hsum]
      _ ≤ ‖W‖ ^ 5 * Real.exp ‖W‖ :=
        Complex.norm_exp_sub_sum_le_norm_mul_exp W 5
      _ ≤ ‖W‖ ^ 5 * Real.exp 1 :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hWnorm)
          (pow_nonneg (norm_nonneg W) 5)
      _ = Real.exp 1 * ‖W‖ ^ 5 := by ring
  have hdecomp :
      Complex.exp W -
        (1 + C + Q + C ^ 2 / 2 + F + S + C * Q + C * F + Q ^ 2 / 2 +
          C ^ 3 / 6 + C ^ 2 * Q / 2 + C ^ 4 / 24) =
        (Complex.exp W - (1 + W + W ^ 2 / 2 + W ^ 3 / 6 + W ^ 4 / 24)) +
          (R + (W ^ 2 - (C ^ 2 + 2 * C * Q + 2 * C * F + Q ^ 2)) / 2 +
            (W ^ 3 - (C ^ 3 + 3 * C ^ 2 * Q)) / 6 +
            (W ^ 4 - C ^ 4) / 24) := by
    rw [hW]
    ring
  rw [hdecomp]
  have hhalf :
      ‖(W ^ 2 - (C ^ 2 + 2 * C * Q + 2 * C * F + Q ^ 2)) / 2‖ ≤
        ‖W ^ 2 - (C ^ 2 + 2 * C * Q + 2 * C * F + Q ^ 2)‖ := by
    rw [norm_div, Complex.norm_ofNat]
    norm_num
  have hsix :
      ‖(W ^ 3 - (C ^ 3 + 3 * C ^ 2 * Q)) / 6‖ ≤
        ‖W ^ 3 - (C ^ 3 + 3 * C ^ 2 * Q)‖ := by
    rw [norm_div, Complex.norm_ofNat]
    have hnon : 0 ≤ ‖W ^ 3 - (C ^ 3 + 3 * C ^ 2 * Q)‖ := norm_nonneg _
    nlinarith
  have htwentyfour :
      ‖(W ^ 4 - C ^ 4) / 24‖ ≤ ‖W ^ 4 - C ^ 4‖ := by
    rw [norm_div, Complex.norm_ofNat]
    have hnon : 0 ≤ ‖W ^ 4 - C ^ 4‖ := norm_nonneg _
    nlinarith
  calc
    ‖(Complex.exp W - (1 + W + W ^ 2 / 2 + W ^ 3 / 6 + W ^ 4 / 24)) +
        (R + (W ^ 2 - (C ^ 2 + 2 * C * Q + 2 * C * F + Q ^ 2)) / 2 +
          (W ^ 3 - (C ^ 3 + 3 * C ^ 2 * Q)) / 6 +
          (W ^ 4 - C ^ 4) / 24)‖
        ≤ ‖Complex.exp W - (1 + W + W ^ 2 / 2 + W ^ 3 / 6 + W ^ 4 / 24)‖ +
            ‖R + (W ^ 2 - (C ^ 2 + 2 * C * Q + 2 * C * F + Q ^ 2)) / 2 +
              (W ^ 3 - (C ^ 3 + 3 * C ^ 2 * Q)) / 6 +
              (W ^ 4 - C ^ 4) / 24‖ := norm_add_le _ _
    _ ≤ Real.exp 1 * ‖W‖ ^ 5 +
          ‖R + (W ^ 2 - (C ^ 2 + 2 * C * Q + 2 * C * F + Q ^ 2)) / 2 +
            (W ^ 3 - (C ^ 3 + 3 * C ^ 2 * Q)) / 6 +
            (W ^ 4 - C ^ 4) / 24‖ := add_le_add htail (le_refl _)
    _ ≤ Real.exp 1 * ‖W‖ ^ 5 +
          (‖R‖ + ‖(W ^ 2 - (C ^ 2 + 2 * C * Q + 2 * C * F + Q ^ 2)) / 2‖ +
            ‖(W ^ 3 - (C ^ 3 + 3 * C ^ 2 * Q)) / 6‖ +
            ‖(W ^ 4 - C ^ 4) / 24‖) := by
          let A : ℂ := (W ^ 2 - (C ^ 2 + 2 * C * Q + 2 * C * F + Q ^ 2)) / 2
          let B : ℂ := (W ^ 3 - (C ^ 3 + 3 * C ^ 2 * Q)) / 6
          let D : ℂ := (W ^ 4 - C ^ 4) / 24
          have htri :
              ‖R + (W ^ 2 - (C ^ 2 + 2 * C * Q + 2 * C * F + Q ^ 2)) / 2 +
                (W ^ 3 - (C ^ 3 + 3 * C ^ 2 * Q)) / 6 +
                (W ^ 4 - C ^ 4) / 24‖ ≤
                ‖R‖ + ‖(W ^ 2 - (C ^ 2 + 2 * C * Q + 2 * C * F + Q ^ 2)) / 2‖ +
                  ‖(W ^ 3 - (C ^ 3 + 3 * C ^ 2 * Q)) / 6‖ +
                  ‖(W ^ 4 - C ^ 4) / 24‖ := by
            change ‖R + A + B + D‖ ≤ ‖R‖ + ‖A‖ + ‖B‖ + ‖D‖
            calc
              ‖R + A + B + D‖ ≤ ‖R + A + B‖ + ‖D‖ := norm_add_le _ _
              _ ≤ (‖R + A‖ + ‖B‖) + ‖D‖ := by
                have hRAB : ‖R + A + B‖ ≤ ‖R + A‖ + ‖B‖ :=
                  norm_add_le (R + A) B
                nlinarith
              _ ≤ ((‖R‖ + ‖A‖) + ‖B‖) + ‖D‖ := by
                have hRA : ‖R + A‖ ≤ ‖R‖ + ‖A‖ := norm_add_le R A
                nlinarith
              _ = ‖R‖ + ‖A‖ + ‖B‖ + ‖D‖ := by ring
          exact add_le_add (le_refl (Real.exp 1 * ‖W‖ ^ 5)) htri
    _ ≤ Real.exp 1 * ‖W‖ ^ 5 + ‖R‖ +
          ‖W ^ 2 - (C ^ 2 + 2 * C * Q + 2 * C * F + Q ^ 2)‖ +
          ‖W ^ 3 - (C ^ 3 + 3 * C ^ 2 * Q)‖ +
          ‖W ^ 4 - C ^ 4‖ := by
          nlinarith [hhalf, hsix, htwentyfour]

private def expPoly6 (z : ℂ) : ℂ :=
  1 + z + z ^ 2 / 2 + z ^ 3 / 6 + z ^ 4 / 24 + z ^ 5 / 120 + z ^ 6 / 720

private def expTail6 (z : ℂ) : ℂ :=
  Complex.exp z - expPoly6 z

private lemma exp_sum_range_seven_eq_expPoly6 (z : ℂ) :
    (∑ m ∈ Finset.range 7, z ^ m / (m.factorial : ℂ)) = expPoly6 z := by
  norm_num [Finset.sum_range_succ, expPoly6]

private lemma expTail6_norm_le_exp6 {z : ℂ} (hz : ‖z‖ ≤ 6) :
    ‖expTail6 z‖ ≤ Real.exp 6 * ‖z‖ ^ 7 := by
  have htail :
      ‖Complex.exp z - (∑ m ∈ Finset.range 7, z ^ m / (m.factorial : ℂ))‖ ≤
        ‖z‖ ^ 7 * Real.exp ‖z‖ :=
    Complex.norm_exp_sub_sum_le_norm_mul_exp z 7
  calc
    ‖expTail6 z‖ =
        ‖Complex.exp z - (∑ m ∈ Finset.range 7, z ^ m / (m.factorial : ℂ))‖ := by
          rw [exp_sum_range_seven_eq_expPoly6]
          rfl
    _ ≤ ‖z‖ ^ 7 * Real.exp ‖z‖ := htail
    _ ≤ ‖z‖ ^ 7 * Real.exp 6 :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hz)
        (pow_nonneg (norm_nonneg z) 7)
    _ = Real.exp 6 * ‖z‖ ^ 7 := by ring

private lemma expTail6_nat_mul_norm_le {w : ℂ} {y : ℝ} (k : ℕ)
    (hk : k ≤ 6) (hw : ‖w‖ = y) (hy1 : y ≤ 1) :
    ‖expTail6 ((k : ℂ) * w)‖ ≤ (k : ℝ) ^ 7 * Real.exp 6 * y ^ 7 := by
  have hkw_norm : ‖(k : ℂ) * w‖ = (k : ℝ) * y := by
    rw [norm_mul, Complex.norm_natCast, hw]
  have hkw_le_six : ‖(k : ℂ) * w‖ ≤ 6 := by
    rw [hkw_norm]
    have hkreal : (k : ℝ) ≤ 6 := by exact_mod_cast hk
    nlinarith
  have hraw := expTail6_norm_le_exp6 (z := (k : ℂ) * w) hkw_le_six
  calc
    ‖expTail6 ((k : ℂ) * w)‖ ≤ Real.exp 6 * ‖(k : ℂ) * w‖ ^ 7 := hraw
    _ = Real.exp 6 * ((k : ℝ) * y) ^ 7 := by rw [hkw_norm]
    _ = (k : ℝ) ^ 7 * Real.exp 6 * y ^ 7 := by ring

private lemma complex_norm_add4_le (z1 z2 z3 z4 : ℂ) :
    ‖z1 + z2 + z3 + z4‖ ≤ ‖z1‖ + ‖z2‖ + ‖z3‖ + ‖z4‖ := by
  have h12 : ‖z1 + z2‖ ≤ ‖z1‖ + ‖z2‖ := norm_add_le z1 z2
  have h123 : ‖z1 + z2 + z3‖ ≤ ‖z1 + z2‖ + ‖z3‖ :=
    norm_add_le (z1 + z2) z3
  have h1234 : ‖z1 + z2 + z3 + z4‖ ≤ ‖z1 + z2 + z3‖ + ‖z4‖ :=
    norm_add_le (z1 + z2 + z3) z4
  nlinarith

private lemma complex_norm_add5_le (z1 z2 z3 z4 z5 : ℂ) :
    ‖z1 + z2 + z3 + z4 + z5‖ ≤
      ‖z1‖ + ‖z2‖ + ‖z3‖ + ‖z4‖ + ‖z5‖ := by
  have h4 := complex_norm_add4_le z1 z2 z3 z4
  have h5 : ‖z1 + z2 + z3 + z4 + z5‖ ≤ ‖z1 + z2 + z3 + z4‖ + ‖z5‖ :=
    norm_add_le (z1 + z2 + z3 + z4) z5
  nlinarith

private lemma complex_norm_add6_le (z1 z2 z3 z4 z5 z6 : ℂ) :
    ‖z1 + z2 + z3 + z4 + z5 + z6‖ ≤
      ‖z1‖ + ‖z2‖ + ‖z3‖ + ‖z4‖ + ‖z5‖ + ‖z6‖ := by
  have h5 := complex_norm_add5_le z1 z2 z3 z4 z5
  have h6 : ‖z1 + z2 + z3 + z4 + z5 + z6‖ ≤
      ‖z1 + z2 + z3 + z4 + z5‖ + ‖z6‖ :=
    norm_add_le (z1 + z2 + z3 + z4 + z5) z6
  nlinarith

private lemma exp_sub_one_sq_remainder_norm_le {w : ℂ} {y : ℝ}
    (hw : ‖w‖ = y) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    ‖(Complex.exp w - 1) ^ 2 -
      (w ^ 2 + w ^ 3 + (7 / 12 : ℂ) * w ^ 4 +
        (1 / 4 : ℂ) * w ^ 5 + (31 / 360 : ℂ) * w ^ 6)‖
      ≤ 1000 * Real.exp 6 * y ^ 7 := by
  let T1 : ℂ := expTail6 w
  let T2 : ℂ := expTail6 (2 * w)
  have hw_le_six : ‖w‖ ≤ 6 := by linarith
  have h2w_norm : ‖(2 : ℂ) * w‖ = 2 * y := by
    rw [norm_mul, Complex.norm_ofNat, hw]
  have h2w_le_six : ‖(2 : ℂ) * w‖ ≤ 6 := by
    rw [h2w_norm]
    nlinarith
  have hT1 : ‖T1‖ ≤ Real.exp 6 * y ^ 7 := by
    simpa [T1, hw] using expTail6_norm_le_exp6 (z := w) hw_le_six
  have hT2 : ‖T2‖ ≤ 200 * Real.exp 6 * y ^ 7 := by
    have hraw := expTail6_norm_le_exp6 (z := (2 : ℂ) * w) h2w_le_six
    calc
      ‖T2‖ ≤ Real.exp 6 * ‖(2 : ℂ) * w‖ ^ 7 := by
        simpa [T2] using hraw
      _ = Real.exp 6 * (2 * y) ^ 7 := by rw [h2w_norm]
      _ = 128 * Real.exp 6 * y ^ 7 := by ring
      _ ≤ 200 * Real.exp 6 * y ^ 7 := by
        have hnon : 0 ≤ Real.exp 6 * y ^ 7 :=
          mul_nonneg (Real.exp_pos 6).le (pow_nonneg hy0 7)
        nlinarith
  have hdiff :
      (Complex.exp w - 1) ^ 2 -
        (w ^ 2 + w ^ 3 + (7 / 12 : ℂ) * w ^ 4 +
          (1 / 4 : ℂ) * w ^ 5 + (31 / 360 : ℂ) * w ^ 6) =
        T2 - 2 * T1 := by
    have hexp2 : Complex.exp (2 * w) = Complex.exp w ^ 2 := by
      simpa using Complex.exp_nat_mul w 2
    dsimp [T1, T2, expTail6, expPoly6]
    rw [hexp2]
    ring_nf
  rw [hdiff]
  calc
    ‖T2 - 2 * T1‖ ≤ ‖T2‖ + ‖2 * T1‖ := norm_sub_le _ _
    _ ≤ 200 * Real.exp 6 * y ^ 7 + 2 * (Real.exp 6 * y ^ 7) := by
      rw [norm_mul, Complex.norm_ofNat]
      exact add_le_add hT2 (mul_le_mul_of_nonneg_left hT1 (by norm_num))
    _ ≤ 1000 * Real.exp 6 * y ^ 7 := by
      have hnon : 0 ≤ Real.exp 6 * y ^ 7 :=
        mul_nonneg (Real.exp_pos 6).le (pow_nonneg hy0 7)
      nlinarith

private lemma exp_sub_one_cube_remainder_norm_le {w : ℂ} {y : ℝ}
    (hw : ‖w‖ = y) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    ‖(Complex.exp w - 1) ^ 3 -
      (w ^ 3 + (3 / 2 : ℂ) * w ^ 4 +
        (5 / 4 : ℂ) * w ^ 5 + (3 / 4 : ℂ) * w ^ 6)‖
      ≤ 10000 * Real.exp 6 * y ^ 7 := by
  let T1 : ℂ := expTail6 w
  let T2 : ℂ := expTail6 (2 * w)
  let T3 : ℂ := expTail6 (3 * w)
  have hw_le_six : ‖w‖ ≤ 6 := by linarith
  have h2w_norm : ‖(2 : ℂ) * w‖ = 2 * y := by
    rw [norm_mul, Complex.norm_ofNat, hw]
  have h3w_norm : ‖(3 : ℂ) * w‖ = 3 * y := by
    rw [norm_mul, Complex.norm_ofNat, hw]
  have h2w_le_six : ‖(2 : ℂ) * w‖ ≤ 6 := by
    rw [h2w_norm]
    nlinarith
  have h3w_le_six : ‖(3 : ℂ) * w‖ ≤ 6 := by
    rw [h3w_norm]
    nlinarith
  have hT1 : ‖T1‖ ≤ Real.exp 6 * y ^ 7 := by
    simpa [T1, hw] using expTail6_norm_le_exp6 (z := w) hw_le_six
  have hT2 : ‖T2‖ ≤ 200 * Real.exp 6 * y ^ 7 := by
    have hraw := expTail6_norm_le_exp6 (z := (2 : ℂ) * w) h2w_le_six
    calc
      ‖T2‖ ≤ Real.exp 6 * ‖(2 : ℂ) * w‖ ^ 7 := by
        simpa [T2] using hraw
      _ = Real.exp 6 * (2 * y) ^ 7 := by rw [h2w_norm]
      _ = 128 * Real.exp 6 * y ^ 7 := by ring
      _ ≤ 200 * Real.exp 6 * y ^ 7 := by
        have hnon : 0 ≤ Real.exp 6 * y ^ 7 :=
          mul_nonneg (Real.exp_pos 6).le (pow_nonneg hy0 7)
        nlinarith
  have hT3 : ‖T3‖ ≤ 3000 * Real.exp 6 * y ^ 7 := by
    have hraw := expTail6_norm_le_exp6 (z := (3 : ℂ) * w) h3w_le_six
    calc
      ‖T3‖ ≤ Real.exp 6 * ‖(3 : ℂ) * w‖ ^ 7 := by
        simpa [T3] using hraw
      _ = Real.exp 6 * (3 * y) ^ 7 := by rw [h3w_norm]
      _ = 2187 * Real.exp 6 * y ^ 7 := by ring
      _ ≤ 3000 * Real.exp 6 * y ^ 7 := by
        have hnon : 0 ≤ Real.exp 6 * y ^ 7 :=
          mul_nonneg (Real.exp_pos 6).le (pow_nonneg hy0 7)
        nlinarith
  have hdiff :
      (Complex.exp w - 1) ^ 3 -
        (w ^ 3 + (3 / 2 : ℂ) * w ^ 4 +
          (5 / 4 : ℂ) * w ^ 5 + (3 / 4 : ℂ) * w ^ 6) =
        T3 - 3 * T2 + 3 * T1 := by
    have hexp2 : Complex.exp (2 * w) = Complex.exp w ^ 2 := by
      simpa using Complex.exp_nat_mul w 2
    have hexp3 : Complex.exp (3 * w) = Complex.exp w ^ 3 := by
      simpa using Complex.exp_nat_mul w 3
    dsimp [T1, T2, T3, expTail6, expPoly6]
    rw [hexp2, hexp3]
    ring_nf
  rw [hdiff]
  calc
    ‖T3 - 3 * T2 + 3 * T1‖ ≤ ‖T3‖ + ‖3 * T2‖ + ‖3 * T1‖ := by
      calc
        ‖T3 - 3 * T2 + 3 * T1‖ ≤ ‖T3 - 3 * T2‖ + ‖3 * T1‖ := norm_add_le _ _
        _ ≤ (‖T3‖ + ‖3 * T2‖) + ‖3 * T1‖ := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_right (norm_sub_le T3 (3 * T2)) ‖3 * T1‖
        _ = ‖T3‖ + ‖3 * T2‖ + ‖3 * T1‖ := by ring
    _ ≤ 3000 * Real.exp 6 * y ^ 7 +
          3 * (200 * Real.exp 6 * y ^ 7) +
            3 * (Real.exp 6 * y ^ 7) := by
      have h3T2 : ‖3 * T2‖ = 3 * ‖T2‖ := by
        rw [norm_mul, Complex.norm_ofNat]
      have h3T1 : ‖3 * T1‖ = 3 * ‖T1‖ := by
        rw [norm_mul, Complex.norm_ofNat]
      rw [h3T2, h3T1]
      nlinarith [hT1, hT2, hT3]
    _ ≤ 10000 * Real.exp 6 * y ^ 7 := by
      have hnon : 0 ≤ Real.exp 6 * y ^ 7 :=
        mul_nonneg (Real.exp_pos 6).le (pow_nonneg hy0 7)
      nlinarith

private lemma exp_sub_one_fourth_remainder_norm_le {w : ℂ} {y : ℝ}
    (hw : ‖w‖ = y) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    ‖(Complex.exp w - 1) ^ 4 -
      (w ^ 4 + 2 * w ^ 5 + (13 / 6 : ℂ) * w ^ 6)‖
      ≤ 100000 * Real.exp 6 * y ^ 7 := by
  let T1 : ℂ := expTail6 w
  let T2 : ℂ := expTail6 (2 * w)
  let T3 : ℂ := expTail6 (3 * w)
  let T4 : ℂ := expTail6 (4 * w)
  have hnon : 0 ≤ Real.exp 6 * y ^ 7 :=
    mul_nonneg (Real.exp_pos 6).le (pow_nonneg hy0 7)
  have hT1 : ‖T1‖ ≤ Real.exp 6 * y ^ 7 := by
    have h := expTail6_nat_mul_norm_le (k := 1) (by norm_num) hw hy1
    simpa [T1] using h
  have hT2 : ‖T2‖ ≤ 200 * Real.exp 6 * y ^ 7 := by
    have h := expTail6_nat_mul_norm_le (k := 2) (by norm_num) hw hy1
    dsimp [T2] at h
    norm_num at h
    nlinarith
  have hT3 : ‖T3‖ ≤ 3000 * Real.exp 6 * y ^ 7 := by
    have h := expTail6_nat_mul_norm_le (k := 3) (by norm_num) hw hy1
    dsimp [T3] at h
    norm_num at h
    nlinarith
  have hT4 : ‖T4‖ ≤ 20000 * Real.exp 6 * y ^ 7 := by
    have h := expTail6_nat_mul_norm_le (k := 4) (by norm_num) hw hy1
    dsimp [T4] at h
    norm_num at h
    nlinarith
  have hdiff :
      (Complex.exp w - 1) ^ 4 -
        (w ^ 4 + 2 * w ^ 5 + (13 / 6 : ℂ) * w ^ 6) =
        T4 - 4 * T3 + 6 * T2 - 4 * T1 := by
    have hexp2 : Complex.exp (2 * w) = Complex.exp w ^ 2 := by
      simpa using Complex.exp_nat_mul w 2
    have hexp3 : Complex.exp (3 * w) = Complex.exp w ^ 3 := by
      simpa using Complex.exp_nat_mul w 3
    have hexp4 : Complex.exp (4 * w) = Complex.exp w ^ 4 := by
      simpa using Complex.exp_nat_mul w 4
    have hq :
        (Complex.exp w - 1) ^ 4 =
          Complex.exp (4 * w) - 4 * Complex.exp (3 * w) +
            6 * Complex.exp (2 * w) - 4 * Complex.exp w + 1 := by
      rw [hexp2, hexp3, hexp4]
      ring
    have hpoly :
        expPoly6 (4 * w) - 4 * expPoly6 (3 * w) + 6 * expPoly6 (2 * w) -
            4 * expPoly6 w =
          -1 + (w ^ 4 + 2 * w ^ 5 + (13 / 6 : ℂ) * w ^ 6) := by
      unfold expPoly6
      ring_nf
    rw [hq]
    dsimp [T1, T2, T3, T4, expTail6]
    calc
      Complex.exp (4 * w) - 4 * Complex.exp (3 * w) + 6 * Complex.exp (2 * w) -
            4 * Complex.exp w + 1 - (w ^ 4 + 2 * w ^ 5 + (13 / 6 : ℂ) * w ^ 6)
          =
        Complex.exp (4 * w) - 4 * Complex.exp (3 * w) + 6 * Complex.exp (2 * w) -
          4 * Complex.exp w -
          (expPoly6 (4 * w) - 4 * expPoly6 (3 * w) + 6 * expPoly6 (2 * w) -
            4 * expPoly6 w) := by
          rw [hpoly]
          ring
      _ = Complex.exp (4 * w) - expPoly6 (4 * w) -
            4 * (Complex.exp (3 * w) - expPoly6 (3 * w)) +
            6 * (Complex.exp (2 * w) - expPoly6 (2 * w)) -
            4 * (Complex.exp w - expPoly6 w) := by ring
  rw [hdiff]
  have htri :
      ‖T4 - 4 * T3 + 6 * T2 - 4 * T1‖ ≤
        ‖T4‖ + ‖4 * T3‖ + ‖6 * T2‖ + ‖4 * T1‖ := by
    have h := complex_norm_add4_le T4 (-(4 * T3)) (6 * T2) (-(4 * T1))
    simpa [sub_eq_add_neg, norm_neg, add_comm, add_left_comm, add_assoc] using h
  calc
    ‖T4 - 4 * T3 + 6 * T2 - 4 * T1‖
        ≤ ‖T4‖ + ‖4 * T3‖ + ‖6 * T2‖ + ‖4 * T1‖ := htri
    _ ≤ 20000 * Real.exp 6 * y ^ 7 +
          4 * (3000 * Real.exp 6 * y ^ 7) +
            6 * (200 * Real.exp 6 * y ^ 7) +
              4 * (Real.exp 6 * y ^ 7) := by
      have h4T3 : ‖4 * T3‖ = 4 * ‖T3‖ := by rw [norm_mul, Complex.norm_ofNat]
      have h6T2 : ‖6 * T2‖ = 6 * ‖T2‖ := by rw [norm_mul, Complex.norm_ofNat]
      have h4T1 : ‖4 * T1‖ = 4 * ‖T1‖ := by rw [norm_mul, Complex.norm_ofNat]
      rw [h4T3, h6T2, h4T1]
      nlinarith [hT1, hT2, hT3, hT4]
    _ ≤ 100000 * Real.exp 6 * y ^ 7 := by
      nlinarith

private lemma exp_sub_one_fifth_remainder_norm_le {w : ℂ} {y : ℝ}
    (hw : ‖w‖ = y) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    ‖(Complex.exp w - 1) ^ 5 - (w ^ 5 + (5 / 2 : ℂ) * w ^ 6)‖
      ≤ 500000 * Real.exp 6 * y ^ 7 := by
  let T1 : ℂ := expTail6 w
  let T2 : ℂ := expTail6 (2 * w)
  let T3 : ℂ := expTail6 (3 * w)
  let T4 : ℂ := expTail6 (4 * w)
  let T5 : ℂ := expTail6 (5 * w)
  have hnon : 0 ≤ Real.exp 6 * y ^ 7 :=
    mul_nonneg (Real.exp_pos 6).le (pow_nonneg hy0 7)
  have hT1 : ‖T1‖ ≤ Real.exp 6 * y ^ 7 := by
    have h := expTail6_nat_mul_norm_le (k := 1) (by norm_num) hw hy1
    simpa [T1] using h
  have hT2 : ‖T2‖ ≤ 200 * Real.exp 6 * y ^ 7 := by
    have h := expTail6_nat_mul_norm_le (k := 2) (by norm_num) hw hy1
    dsimp [T2] at h
    norm_num at h
    nlinarith
  have hT3 : ‖T3‖ ≤ 3000 * Real.exp 6 * y ^ 7 := by
    have h := expTail6_nat_mul_norm_le (k := 3) (by norm_num) hw hy1
    dsimp [T3] at h
    norm_num at h
    nlinarith
  have hT4 : ‖T4‖ ≤ 20000 * Real.exp 6 * y ^ 7 := by
    have h := expTail6_nat_mul_norm_le (k := 4) (by norm_num) hw hy1
    dsimp [T4] at h
    norm_num at h
    nlinarith
  have hT5 : ‖T5‖ ≤ 80000 * Real.exp 6 * y ^ 7 := by
    have h := expTail6_nat_mul_norm_le (k := 5) (by norm_num) hw hy1
    dsimp [T5] at h
    norm_num at h
    nlinarith
  have hdiff :
      (Complex.exp w - 1) ^ 5 - (w ^ 5 + (5 / 2 : ℂ) * w ^ 6) =
        T5 - 5 * T4 + 10 * T3 - 10 * T2 + 5 * T1 := by
    have hexp2 : Complex.exp (2 * w) = Complex.exp w ^ 2 := by
      simpa using Complex.exp_nat_mul w 2
    have hexp3 : Complex.exp (3 * w) = Complex.exp w ^ 3 := by
      simpa using Complex.exp_nat_mul w 3
    have hexp4 : Complex.exp (4 * w) = Complex.exp w ^ 4 := by
      simpa using Complex.exp_nat_mul w 4
    have hexp5 : Complex.exp (5 * w) = Complex.exp w ^ 5 := by
      simpa using Complex.exp_nat_mul w 5
    have hq :
        (Complex.exp w - 1) ^ 5 =
          Complex.exp (5 * w) - 5 * Complex.exp (4 * w) +
            10 * Complex.exp (3 * w) - 10 * Complex.exp (2 * w) +
              5 * Complex.exp w - 1 := by
      rw [hexp2, hexp3, hexp4, hexp5]
      ring
    have hpoly :
        expPoly6 (5 * w) - 5 * expPoly6 (4 * w) + 10 * expPoly6 (3 * w) -
            10 * expPoly6 (2 * w) + 5 * expPoly6 w =
          1 + (w ^ 5 + (5 / 2 : ℂ) * w ^ 6) := by
      unfold expPoly6
      ring_nf
    rw [hq]
    dsimp [T1, T2, T3, T4, T5, expTail6]
    calc
      Complex.exp (5 * w) - 5 * Complex.exp (4 * w) + 10 * Complex.exp (3 * w) -
            10 * Complex.exp (2 * w) + 5 * Complex.exp w - 1 -
            (w ^ 5 + (5 / 2 : ℂ) * w ^ 6)
          =
        Complex.exp (5 * w) - 5 * Complex.exp (4 * w) + 10 * Complex.exp (3 * w) -
          10 * Complex.exp (2 * w) + 5 * Complex.exp w -
          (expPoly6 (5 * w) - 5 * expPoly6 (4 * w) + 10 * expPoly6 (3 * w) -
            10 * expPoly6 (2 * w) + 5 * expPoly6 w) := by
          rw [hpoly]
          ring
      _ = Complex.exp (5 * w) - expPoly6 (5 * w) -
            5 * (Complex.exp (4 * w) - expPoly6 (4 * w)) +
            10 * (Complex.exp (3 * w) - expPoly6 (3 * w)) -
            10 * (Complex.exp (2 * w) - expPoly6 (2 * w)) +
            5 * (Complex.exp w - expPoly6 w) := by ring
  rw [hdiff]
  have htri :
      ‖T5 - 5 * T4 + 10 * T3 - 10 * T2 + 5 * T1‖ ≤
        ‖T5‖ + ‖5 * T4‖ + ‖10 * T3‖ + ‖10 * T2‖ + ‖5 * T1‖ := by
    have h := complex_norm_add5_le T5 (-(5 * T4)) (10 * T3) (-(10 * T2)) (5 * T1)
    simpa [sub_eq_add_neg, norm_neg, add_comm, add_left_comm, add_assoc] using h
  calc
    ‖T5 - 5 * T4 + 10 * T3 - 10 * T2 + 5 * T1‖
        ≤ ‖T5‖ + ‖5 * T4‖ + ‖10 * T3‖ + ‖10 * T2‖ + ‖5 * T1‖ := htri
    _ ≤ 80000 * Real.exp 6 * y ^ 7 +
          5 * (20000 * Real.exp 6 * y ^ 7) +
            10 * (3000 * Real.exp 6 * y ^ 7) +
              10 * (200 * Real.exp 6 * y ^ 7) +
                5 * (Real.exp 6 * y ^ 7) := by
      have h5T4 : ‖5 * T4‖ = 5 * ‖T4‖ := by rw [norm_mul, Complex.norm_ofNat]
      have h10T3 : ‖10 * T3‖ = 10 * ‖T3‖ := by rw [norm_mul, Complex.norm_ofNat]
      have h10T2 : ‖10 * T2‖ = 10 * ‖T2‖ := by rw [norm_mul, Complex.norm_ofNat]
      have h5T1 : ‖5 * T1‖ = 5 * ‖T1‖ := by rw [norm_mul, Complex.norm_ofNat]
      rw [h5T4, h10T3, h10T2, h5T1]
      nlinarith [hT1, hT2, hT3, hT4, hT5]
    _ ≤ 500000 * Real.exp 6 * y ^ 7 := by
      nlinarith

private lemma exp_sub_one_sixth_remainder_norm_le {w : ℂ} {y : ℝ}
    (hw : ‖w‖ = y) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    ‖(Complex.exp w - 1) ^ 6 - w ^ 6‖
      ≤ 2000000 * Real.exp 6 * y ^ 7 := by
  let T1 : ℂ := expTail6 w
  let T2 : ℂ := expTail6 (2 * w)
  let T3 : ℂ := expTail6 (3 * w)
  let T4 : ℂ := expTail6 (4 * w)
  let T5 : ℂ := expTail6 (5 * w)
  let T6 : ℂ := expTail6 (6 * w)
  have hnon : 0 ≤ Real.exp 6 * y ^ 7 :=
    mul_nonneg (Real.exp_pos 6).le (pow_nonneg hy0 7)
  have hT1 : ‖T1‖ ≤ Real.exp 6 * y ^ 7 := by
    have h := expTail6_nat_mul_norm_le (k := 1) (by norm_num) hw hy1
    simpa [T1] using h
  have hT2 : ‖T2‖ ≤ 200 * Real.exp 6 * y ^ 7 := by
    have h := expTail6_nat_mul_norm_le (k := 2) (by norm_num) hw hy1
    dsimp [T2] at h
    norm_num at h
    nlinarith
  have hT3 : ‖T3‖ ≤ 3000 * Real.exp 6 * y ^ 7 := by
    have h := expTail6_nat_mul_norm_le (k := 3) (by norm_num) hw hy1
    dsimp [T3] at h
    norm_num at h
    nlinarith
  have hT4 : ‖T4‖ ≤ 20000 * Real.exp 6 * y ^ 7 := by
    have h := expTail6_nat_mul_norm_le (k := 4) (by norm_num) hw hy1
    dsimp [T4] at h
    norm_num at h
    nlinarith
  have hT5 : ‖T5‖ ≤ 80000 * Real.exp 6 * y ^ 7 := by
    have h := expTail6_nat_mul_norm_le (k := 5) (by norm_num) hw hy1
    dsimp [T5] at h
    norm_num at h
    nlinarith
  have hT6 : ‖T6‖ ≤ 300000 * Real.exp 6 * y ^ 7 := by
    have h := expTail6_nat_mul_norm_le (k := 6) (by norm_num) hw hy1
    dsimp [T6] at h
    norm_num at h
    nlinarith
  have hdiff :
      (Complex.exp w - 1) ^ 6 - w ^ 6 =
        T6 - 6 * T5 + 15 * T4 - 20 * T3 + 15 * T2 - 6 * T1 := by
    have hexp2 : Complex.exp (2 * w) = Complex.exp w ^ 2 := by
      simpa using Complex.exp_nat_mul w 2
    have hexp3 : Complex.exp (3 * w) = Complex.exp w ^ 3 := by
      simpa using Complex.exp_nat_mul w 3
    have hexp4 : Complex.exp (4 * w) = Complex.exp w ^ 4 := by
      simpa using Complex.exp_nat_mul w 4
    have hexp5 : Complex.exp (5 * w) = Complex.exp w ^ 5 := by
      simpa using Complex.exp_nat_mul w 5
    have hexp6 : Complex.exp (6 * w) = Complex.exp w ^ 6 := by
      simpa using Complex.exp_nat_mul w 6
    have hq :
        (Complex.exp w - 1) ^ 6 =
          Complex.exp (6 * w) - 6 * Complex.exp (5 * w) +
            15 * Complex.exp (4 * w) - 20 * Complex.exp (3 * w) +
              15 * Complex.exp (2 * w) - 6 * Complex.exp w + 1 := by
      rw [hexp2, hexp3, hexp4, hexp5, hexp6]
      ring
    have hpoly :
        expPoly6 (6 * w) - 6 * expPoly6 (5 * w) + 15 * expPoly6 (4 * w) -
            20 * expPoly6 (3 * w) + 15 * expPoly6 (2 * w) - 6 * expPoly6 w =
          -1 + w ^ 6 := by
      unfold expPoly6
      ring_nf
    rw [hq]
    dsimp [T1, T2, T3, T4, T5, T6, expTail6]
    calc
      Complex.exp (6 * w) - 6 * Complex.exp (5 * w) + 15 * Complex.exp (4 * w) -
            20 * Complex.exp (3 * w) + 15 * Complex.exp (2 * w) -
            6 * Complex.exp w + 1 - w ^ 6
          =
        Complex.exp (6 * w) - 6 * Complex.exp (5 * w) + 15 * Complex.exp (4 * w) -
          20 * Complex.exp (3 * w) + 15 * Complex.exp (2 * w) - 6 * Complex.exp w -
          (expPoly6 (6 * w) - 6 * expPoly6 (5 * w) + 15 * expPoly6 (4 * w) -
            20 * expPoly6 (3 * w) + 15 * expPoly6 (2 * w) - 6 * expPoly6 w) := by
          rw [hpoly]
          ring
      _ = Complex.exp (6 * w) - expPoly6 (6 * w) -
            6 * (Complex.exp (5 * w) - expPoly6 (5 * w)) +
            15 * (Complex.exp (4 * w) - expPoly6 (4 * w)) -
            20 * (Complex.exp (3 * w) - expPoly6 (3 * w)) +
            15 * (Complex.exp (2 * w) - expPoly6 (2 * w)) -
            6 * (Complex.exp w - expPoly6 w) := by ring
  rw [hdiff]
  have htri :
      ‖T6 - 6 * T5 + 15 * T4 - 20 * T3 + 15 * T2 - 6 * T1‖ ≤
        ‖T6‖ + ‖6 * T5‖ + ‖15 * T4‖ + ‖20 * T3‖ +
          ‖15 * T2‖ + ‖6 * T1‖ := by
    have h := complex_norm_add6_le T6 (-(6 * T5)) (15 * T4) (-(20 * T3))
      (15 * T2) (-(6 * T1))
    simpa [sub_eq_add_neg, norm_neg, add_comm, add_left_comm, add_assoc] using h
  calc
    ‖T6 - 6 * T5 + 15 * T4 - 20 * T3 + 15 * T2 - 6 * T1‖
        ≤ ‖T6‖ + ‖6 * T5‖ + ‖15 * T4‖ + ‖20 * T3‖ +
          ‖15 * T2‖ + ‖6 * T1‖ := htri
    _ ≤ 300000 * Real.exp 6 * y ^ 7 +
          6 * (80000 * Real.exp 6 * y ^ 7) +
            15 * (20000 * Real.exp 6 * y ^ 7) +
              20 * (3000 * Real.exp 6 * y ^ 7) +
                15 * (200 * Real.exp 6 * y ^ 7) +
                  6 * (Real.exp 6 * y ^ 7) := by
      have h6T5 : ‖6 * T5‖ = 6 * ‖T5‖ := by rw [norm_mul, Complex.norm_ofNat]
      have h15T4 : ‖15 * T4‖ = 15 * ‖T4‖ := by rw [norm_mul, Complex.norm_ofNat]
      have h20T3 : ‖20 * T3‖ = 20 * ‖T3‖ := by rw [norm_mul, Complex.norm_ofNat]
      have h15T2 : ‖15 * T2‖ = 15 * ‖T2‖ := by rw [norm_mul, Complex.norm_ofNat]
      have h6T1 : ‖6 * T1‖ = 6 * ‖T1‖ := by rw [norm_mul, Complex.norm_ofNat]
      rw [h6T5, h15T4, h20T3, h15T2, h6T1]
      nlinarith [hT1, hT2, hT3, hT4, hT5, hT6]
    _ ≤ 2000000 * Real.exp 6 * y ^ 7 := by
      nlinarith

private lemma fragPermLocalExponent_seventh_remainder_norm_le {r θ : ℝ}
    (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1)
    (hθδ : |θ| ≤ fragPermThirdSaddleDeltaReal r)
    (hδle : fragPermThirdSaddleDeltaReal r ≤ 1)
    (hδu : fragPermThirdSaddleDeltaReal r ≤ (1 - r) / 4) :
    ‖fragPermLocalExponent r θ -
        (-Complex.I * ((fragPermSaddleB3Real r : ℂ) / 6) * (θ : ℂ) ^ 3 +
          ((fragPermSaddleB4Real r : ℂ) / 24) * (θ : ℂ) ^ 4 +
          Complex.I * ((fragPermSaddleB5Real r : ℂ) / 120) * (θ : ℂ) ^ 5 -
          ((fragPermSaddleB6Real r : ℂ) / 720) * (θ : ℂ) ^ 6)‖
      ≤ 1000000000 * Real.exp 6 * |θ| ^ 7 / (1 - r) ^ 8 := by
  let y : ℝ := |θ|
  let uR : ℝ := 1 - r
  let u : ℂ := 1 - (r : ℂ)
  let w : ℂ := (θ : ℂ) * Complex.I
  let q : ℂ := Complex.exp w - 1
  let c : ℂ := (r : ℂ) / u
  let geom : ℂ := (r : ℂ) * q / u
  let A : ℂ := (r : ℂ) / u ^ 2
  let B : ℂ := (r : ℂ) ^ 2 / u ^ 3
  let D : ℂ := (r : ℂ) ^ 3 / u ^ 4
  let P1 : ℂ := w ^ 3 / 6 + w ^ 4 / 24 + w ^ 5 / 120 + w ^ 6 / 720
  let P2 : ℂ := w ^ 3 + (7 / 12 : ℂ) * w ^ 4 + (1 / 4 : ℂ) * w ^ 5 +
    (31 / 360 : ℂ) * w ^ 6
  let P3 : ℂ := w ^ 3 + ((3 / 2 : ℂ) + c) * w ^ 4 +
    ((5 / 4 : ℂ) + 2 * c + c ^ 2) * w ^ 5 +
      ((3 / 4 : ℂ) + (13 / 6 : ℂ) * c + (5 / 2 : ℂ) * c ^ 2 + c ^ 3) *
        w ^ 6
  let P : ℂ :=
    -Complex.I * ((fragPermSaddleB3Real r : ℂ) / 6) * (θ : ℂ) ^ 3 +
      ((fragPermSaddleB4Real r : ℂ) / 24) * (θ : ℂ) ^ 4 +
        Complex.I * ((fragPermSaddleB5Real r : ℂ) / 120) * (θ : ℂ) ^ 5 -
          ((fragPermSaddleB6Real r : ℂ) / 720) * (θ : ℂ) ^ 6
  have hrpos : 0 < r := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hr.1
  have hr0 : 0 ≤ r := hrpos.le
  have hrle : r ≤ 1 := hr.2.le
  have hu_pos : 0 < uR := by dsimp [uR]; linarith [hr.2]
  have hu_nonneg : 0 ≤ uR := hu_pos.le
  have hu_le_one : uR ≤ 1 := by dsimp [uR]; linarith [hr.1]
  have hu_ne : u ≠ 0 := by
    dsimp [u]
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  have huR_ne : uR ≠ 0 := hu_pos.ne'
  have hy0 : 0 ≤ y := by dsimp [y]; exact abs_nonneg θ
  have hy1 : y ≤ 1 := by dsimp [y]; exact hθδ.trans hδle
  have hr_norm : ‖(r : ℂ)‖ = r :=
    (RCLike.norm_ofReal (K := ℂ) r).trans (abs_of_nonneg hr0)
  have hu_norm : ‖u‖ = uR := by
    dsimp [u, uR]
    have hcoerce : (1 : ℂ) - (r : ℂ) = ((1 - r : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [hcoerce]
    exact (RCLike.norm_ofReal (K := ℂ) (1 - r)).trans (abs_of_pos hu_pos)
  have hw_norm : ‖w‖ = y := by
    dsimp [w, y]
    simp
  have hθone : |θ| ≤ 1 := by simpa [y] using hy1
  have hq_norm : ‖q‖ ≤ 2 * y := by
    simpa [q, w, y] using fragPerm_exp_i_sub_one_norm_le_two_abs hθone
  have hgeom_norm : ‖geom‖ ≤ (1 / 2 : ℝ) := by
    have hnorm_eq : ‖geom‖ = r * ‖q‖ / uR := by
      dsimp [geom, c, u, uR]
      rw [norm_div, norm_mul, hr_norm, hu_norm]
    calc
      ‖geom‖ = r * ‖q‖ / uR := hnorm_eq
      _ ≤ r * (2 * y) / uR := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hq_norm hr0) hu_nonneg
      _ ≤ 1 * (2 * fragPermThirdSaddleDeltaReal r) / uR := by
        have hyδ : y ≤ fragPermThirdSaddleDeltaReal r := by simpa [y] using hθδ
        exact div_le_div_of_nonneg_right
          (mul_le_mul hrle (mul_le_mul_of_nonneg_left hyδ (by norm_num))
            (mul_nonneg (by norm_num) hy0) zero_le_one) hu_nonneg
      _ ≤ 1 / 2 := by
        rw [one_mul]
        have hδu' : 2 * fragPermThirdSaddleDeltaReal r ≤ uR / 2 := by
          have hδu0 : fragPermThirdSaddleDeltaReal r ≤ uR / 4 := by
            simpa [uR] using hδu
          linarith
        rw [div_le_iff₀ hu_pos]
        simpa [one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hδu'
  have hgeom_ne : (1 : ℂ) - geom ≠ 0 := by
    intro hzero
    have hgeom_eq : geom = 1 := by exact sub_eq_zero.mp hzero |>.symm
    have : (1 : ℝ) ≤ (1 / 2 : ℝ) := by
      simpa [hgeom_eq] using hgeom_norm
    norm_num at this
  have hinv_geom_norm : ‖(1 - geom)⁻¹‖ ≤ 2 := by
    have hdist : (1 / 2 : ℝ) ≤ ‖1 - geom‖ := by
      calc
        (1 / 2 : ℝ) ≤ 1 - ‖geom‖ := by linarith [hgeom_norm]
        _ ≤ ‖(1 : ℂ) - geom‖ := by
          have h := norm_sub_norm_le (1 : ℂ) geom
          have hone : ‖(1 : ℂ)‖ = (1 : ℝ) := by norm_num
          rw [hone] at h
          linarith
    rw [norm_inv]
    have hnorm_pos : 0 < ‖(1 : ℂ) - geom‖ := norm_pos_iff.mpr hgeom_ne
    rw [inv_le_comm₀ hnorm_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [hdist]
  have hdecomp := fragPermLocalExponent_decomp (r := r) (θ := θ) hr.2 hgeom_ne
  dsimp [u, w, q, geom, c] at hdecomp
  have hP_decomp : P = A * P1 + B * P2 + D * P3 := by
    have hu_eq : u = (uR : ℂ) := by
      dsimp [u, uR]
      norm_num
    have h1mr_ne : 1 - r ≠ 0 := by linarith [hr.2]
    have hw3 : w ^ 3 = -Complex.I * (θ : ℂ) ^ 3 := by
      dsimp [w]
      rw [mul_pow, Complex.I_pow_three]
      ring
    have hw4 : w ^ 4 = (θ : ℂ) ^ 4 := by
      dsimp [w]
      rw [mul_pow, Complex.I_pow_four]
      ring
    have hw5 : w ^ 5 = Complex.I * (θ : ℂ) ^ 5 := by
      dsimp [w]
      have hI5 : Complex.I ^ 5 = Complex.I := by
        calc
          Complex.I ^ 5 = Complex.I ^ 4 * Complex.I := by ring
          _ = Complex.I := by rw [Complex.I_pow_four, one_mul]
      rw [mul_pow, hI5]
      ring
    have hw6 : w ^ 6 = -((θ : ℂ) ^ 6) := by
      dsimp [w]
      have hI6 : Complex.I ^ 6 = -1 := by
        calc
          Complex.I ^ 6 = Complex.I ^ 4 * Complex.I ^ 2 := by ring
          _ = -1 := by
            rw [Complex.I_pow_four, Complex.I_sq]
            ring
      rw [mul_pow, hI6]
      ring
    have hb3idR :
        fragPermSaddleB3Real r / 6 =
          r / (6 * uR ^ 2) + r ^ 2 / uR ^ 3 + r ^ 3 / uR ^ 4 := by
      unfold fragPermSaddleB3Real
      dsimp [uR]
      field_simp [h1mr_ne]
      ring
    have hb4idR :
        fragPermSaddleB4Real r / 24 =
          r / (24 * uR ^ 2) + 7 * r ^ 2 / (12 * uR ^ 3) +
            3 * r ^ 3 / (2 * uR ^ 4) + r ^ 4 / uR ^ 5 := by
      unfold fragPermSaddleB4Real
      dsimp [uR]
      field_simp [h1mr_ne]
      ring
    have hb5idR :
        fragPermSaddleB5Real r / 120 =
          r / (120 * uR ^ 2) + r ^ 2 / (4 * uR ^ 3) +
            r ^ 3 / uR ^ 4 * (5 / 4 + 2 * (r / uR) + (r / uR) ^ 2) := by
      unfold fragPermSaddleB5Real
      dsimp [uR]
      field_simp [h1mr_ne]
      ring
    have hb6idR :
        fragPermSaddleB6Real r / 720 =
          r / (720 * uR ^ 2) + 31 * r ^ 2 / (360 * uR ^ 3) +
            r ^ 3 / uR ^ 4 *
              (3 / 4 + 13 / 6 * (r / uR) + 5 / 2 * (r / uR) ^ 2 +
                (r / uR) ^ 3) := by
      unfold fragPermSaddleB6Real
      dsimp [uR]
      field_simp [h1mr_ne]
      ring
    have hb3id :
        ((fragPermSaddleB3Real r : ℂ) / 6) =
          ((r / (6 * uR ^ 2) + r ^ 2 / uR ^ 3 + r ^ 3 / uR ^ 4 : ℝ) : ℂ) := by
      norm_num [← Complex.ofReal_div]
      exact_mod_cast hb3idR
    have hb4id :
        ((fragPermSaddleB4Real r : ℂ) / 24) =
          ((r / (24 * uR ^ 2) + 7 * r ^ 2 / (12 * uR ^ 3) +
            3 * r ^ 3 / (2 * uR ^ 4) + r ^ 4 / uR ^ 5 : ℝ) : ℂ) := by
      norm_num [← Complex.ofReal_div]
      exact_mod_cast hb4idR
    have hb5id :
        ((fragPermSaddleB5Real r : ℂ) / 120) =
          ((r / (120 * uR ^ 2) + r ^ 2 / (4 * uR ^ 3) +
            r ^ 3 / uR ^ 4 * (5 / 4 + 2 * (r / uR) + (r / uR) ^ 2) : ℝ) : ℂ) := by
      rw [show ((fragPermSaddleB5Real r : ℂ) / 120) =
          ((fragPermSaddleB5Real r / 120 : ℝ) : ℂ) by norm_num]
      exact_mod_cast hb5idR
    have hb6id :
        ((fragPermSaddleB6Real r : ℂ) / 720) =
          ((r / (720 * uR ^ 2) + 31 * r ^ 2 / (360 * uR ^ 3) +
            r ^ 3 / uR ^ 4 *
              (3 / 4 + 13 / 6 * (r / uR) + 5 / 2 * (r / uR) ^ 2 +
                (r / uR) ^ 3) : ℝ) : ℂ) := by
      rw [show ((fragPermSaddleB6Real r : ℂ) / 720) =
          ((fragPermSaddleB6Real r / 720 : ℝ) : ℂ) by norm_num]
      exact_mod_cast hb6idR
    have hcoef3 :
        A / 6 + B + D = ((fragPermSaddleB3Real r : ℂ) / 6) := by
      rw [hb3id]
      dsimp [A, B, D]
      rw [hu_eq]
      norm_num [Complex.ofReal_div, Complex.ofReal_pow]
      field_simp [huR_ne]
    have hcoef4 :
        A / 24 + (7 / 12 : ℂ) * B + ((3 / 2 : ℂ) + c) * D =
          ((fragPermSaddleB4Real r : ℂ) / 24) := by
      rw [hb4id]
      dsimp [A, B, D, c]
      rw [hu_eq]
      norm_num [Complex.ofReal_div, Complex.ofReal_pow]
      field_simp [huR_ne]
      ring
    have hcoef5 :
        A / 120 + (1 / 4 : ℂ) * B + ((5 / 4 : ℂ) + 2 * c + c ^ 2) * D =
          ((fragPermSaddleB5Real r : ℂ) / 120) := by
      rw [hb5id]
      dsimp [A, B, D, c]
      rw [hu_eq]
      norm_num [Complex.ofReal_div, Complex.ofReal_pow]
      field_simp [huR_ne]
    have hcoef6 :
        A / 720 + (31 / 360 : ℂ) * B +
            ((3 / 4 : ℂ) + (13 / 6 : ℂ) * c + (5 / 2 : ℂ) * c ^ 2 + c ^ 3) * D =
          ((fragPermSaddleB6Real r : ℂ) / 720) := by
      rw [hb6id]
      dsimp [A, B, D, c]
      rw [hu_eq]
      norm_num [Complex.ofReal_div, Complex.ofReal_pow]
      field_simp [huR_ne]
    have hcollect :
        A * P1 + B * P2 + D * P3 =
          (A / 6 + B + D) * w ^ 3 +
          (A / 24 + (7 / 12 : ℂ) * B + ((3 / 2 : ℂ) + c) * D) * w ^ 4 +
          (A / 120 + (1 / 4 : ℂ) * B + ((5 / 4 : ℂ) + 2 * c + c ^ 2) * D) *
            w ^ 5 +
          (A / 720 + (31 / 360 : ℂ) * B +
            ((3 / 4 : ℂ) + (13 / 6 : ℂ) * c + (5 / 2 : ℂ) * c ^ 2 + c ^ 3) * D) *
            w ^ 6 := by
      dsimp [P1, P2, P3]
      ring
    rw [hcollect]
    dsimp [P]
    rw [hcoef3, hcoef4, hcoef5, hcoef6, hw3, hw4, hw5, hw6]
    ring
  have hR1 :
      ‖ExpStirling.expLocalRemainder θ - P1‖ ≤ Real.exp 6 * y ^ 7 := by
    have htail := expTail6_norm_le_exp6 (z := w) (by simpa [hw_norm] using (by linarith : y ≤ 6))
    have htail' : ‖expTail6 w‖ ≤ Real.exp 6 * y ^ 7 := by
      simpa [hw_norm] using htail
    have htail_eq : expTail6 w = ExpStirling.expLocalRemainder θ - P1 := by
      dsimp [expTail6, expPoly6, P1, w]
      rw [ExpStirling.expLocalRemainder_eq θ]
      ring_nf
      norm_num [Complex.ofReal_mul]
      ring
    simpa [htail_eq]
      using htail'
  have hR2 :
      ‖(q ^ 2 - w ^ 2) - P2‖ ≤ 1000 * Real.exp 6 * y ^ 7 := by
    have h := exp_sub_one_sq_remainder_norm_le (w := w) (y := y) hw_norm hy0 hy1
    simpa [q, P2, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
  have hR3 :
      ‖q ^ 3 - (w ^ 3 + (3 / 2 : ℂ) * w ^ 4 +
          (5 / 4 : ℂ) * w ^ 5 + (3 / 4 : ℂ) * w ^ 6)‖
        ≤ 10000 * Real.exp 6 * y ^ 7 := by
    simpa [q] using exp_sub_one_cube_remainder_norm_le (w := w) (y := y) hw_norm hy0 hy1
  have hR4 :
      ‖q ^ 4 - (w ^ 4 + 2 * w ^ 5 + (13 / 6 : ℂ) * w ^ 6)‖
        ≤ 100000 * Real.exp 6 * y ^ 7 := by
    simpa [q] using exp_sub_one_fourth_remainder_norm_le (w := w) (y := y) hw_norm hy0 hy1
  have hR5 :
      ‖q ^ 5 - (w ^ 5 + (5 / 2 : ℂ) * w ^ 6)‖
        ≤ 500000 * Real.exp 6 * y ^ 7 := by
    simpa [q] using exp_sub_one_fifth_remainder_norm_le (w := w) (y := y) hw_norm hy0 hy1
  have hR6 :
      ‖q ^ 6 - w ^ 6‖ ≤ 2000000 * Real.exp 6 * y ^ 7 := by
    simpa [q] using exp_sub_one_sixth_remainder_norm_le (w := w) (y := y) hw_norm hy0 hy1
  have hA_norm : ‖A‖ = r / uR ^ 2 := by
    dsimp [A, u, uR]
    rw [norm_div, norm_pow, hr_norm, hu_norm]
  have hB_norm : ‖B‖ = r ^ 2 / uR ^ 3 := by
    dsimp [B, u, uR]
    rw [norm_div, norm_pow, norm_pow, hr_norm, hu_norm]
  have hD_norm : ‖D‖ = r ^ 3 / uR ^ 4 := by
    dsimp [D, u, uR]
    rw [norm_div, norm_pow, norm_pow, hr_norm, hu_norm]
  have hc_norm : ‖c‖ = r / uR := by
    dsimp [c, u, uR]
    rw [norm_div, hr_norm, hu_norm]
  have hden8_pos : 0 < uR ^ 8 := by positivity
  have hpow_le {k : ℕ} (hk : k ≤ 8) :
      uR ^ 8 ≤ uR ^ k := by
    have hsplit : uR ^ 8 = uR ^ k * uR ^ (8 - k) := by
      rw [← pow_add, Nat.add_sub_of_le hk]
    rw [hsplit]
    have hpow_nonneg : 0 ≤ uR ^ k := pow_nonneg hu_nonneg k
    have hrest_le_one : uR ^ (8 - k) ≤ 1 := by
      calc
        uR ^ (8 - k) ≤ 1 ^ (8 - k) := pow_le_pow_left₀ hu_nonneg hu_le_one _
        _ = 1 := by simp
    exact mul_le_of_le_one_right hpow_nonneg hrest_le_one
  have hdiv_le8 {k : ℕ} (hk : k ≤ 8) {C : ℝ} (hC : 0 ≤ C) :
      C / uR ^ k ≤ C / uR ^ 8 :=
    div_le_div_of_nonneg_left hC hden8_pos (hpow_le hk)
  have hAterm :
      ‖A * (ExpStirling.expLocalRemainder θ - P1)‖
        ≤ 1000 * Real.exp 6 * y ^ 7 / uR ^ 8 := by
    calc
      ‖A * (ExpStirling.expLocalRemainder θ - P1)‖ =
          ‖A‖ * ‖ExpStirling.expLocalRemainder θ - P1‖ := norm_mul _ _
      _ ≤ (r / uR ^ 2) * (Real.exp 6 * y ^ 7) :=
        mul_le_mul hA_norm.le hR1 (norm_nonneg _) (by positivity)
      _ ≤ Real.exp 6 * y ^ 7 / uR ^ 2 := by
        have hbase_nonneg : 0 ≤ Real.exp 6 * y ^ 7 :=
          mul_nonneg (Real.exp_pos 6).le (pow_nonneg hy0 7)
        have hrbase : r * (Real.exp 6 * y ^ 7) ≤ 1 * (Real.exp 6 * y ^ 7) :=
          mul_le_mul_of_nonneg_right hrle hbase_nonneg
        calc
          (r / uR ^ 2) * (Real.exp 6 * y ^ 7) =
              (r * (Real.exp 6 * y ^ 7)) / uR ^ 2 := by ring
          _ ≤ (1 * (Real.exp 6 * y ^ 7)) / uR ^ 2 :=
              div_le_div_of_nonneg_right hrbase (pow_nonneg hu_nonneg 2)
          _ = Real.exp 6 * y ^ 7 / uR ^ 2 := by ring
      _ ≤ Real.exp 6 * y ^ 7 / uR ^ 8 :=
        hdiv_le8 (by norm_num : 2 ≤ 8)
          (mul_nonneg (Real.exp_pos 6).le (pow_nonneg hy0 7))
      _ ≤ 1000 * Real.exp 6 * y ^ 7 / uR ^ 8 := by
        exact div_le_div_of_nonneg_right
          (by nlinarith [mul_nonneg (Real.exp_pos 6).le (pow_nonneg hy0 7)])
          (pow_nonneg hu_nonneg 8)
  have hBterm :
      ‖B * ((q ^ 2 - w ^ 2) - P2)‖
        ≤ 1000000 * Real.exp 6 * y ^ 7 / uR ^ 8 := by
    calc
      ‖B * ((q ^ 2 - w ^ 2) - P2)‖ =
          ‖B‖ * ‖(q ^ 2 - w ^ 2) - P2‖ := norm_mul _ _
      _ ≤ (r ^ 2 / uR ^ 3) * (1000 * Real.exp 6 * y ^ 7) :=
        mul_le_mul hB_norm.le hR2 (norm_nonneg _) (by positivity)
      _ ≤ 1000 * Real.exp 6 * y ^ 7 / uR ^ 3 := by
        have hr2le : r ^ 2 ≤ 1 := by nlinarith [hr0, hrle]
        have hbase_nonneg : 0 ≤ 1000 * Real.exp 6 * y ^ 7 :=
          mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos 6).le)
            (pow_nonneg hy0 7)
        have hrbase : r ^ 2 * (1000 * Real.exp 6 * y ^ 7) ≤
            1 * (1000 * Real.exp 6 * y ^ 7) :=
          mul_le_mul_of_nonneg_right hr2le hbase_nonneg
        calc
          (r ^ 2 / uR ^ 3) * (1000 * Real.exp 6 * y ^ 7) =
              (r ^ 2 * (1000 * Real.exp 6 * y ^ 7)) / uR ^ 3 := by ring
          _ ≤ (1 * (1000 * Real.exp 6 * y ^ 7)) / uR ^ 3 :=
              div_le_div_of_nonneg_right hrbase (pow_nonneg hu_nonneg 3)
          _ = 1000 * Real.exp 6 * y ^ 7 / uR ^ 3 := by ring
      _ ≤ 1000 * Real.exp 6 * y ^ 7 / uR ^ 8 :=
        hdiv_le8 (by norm_num : 3 ≤ 8)
          (mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos 6).le)
            (pow_nonneg hy0 7))
      _ ≤ 1000000 * Real.exp 6 * y ^ 7 / uR ^ 8 := by
        exact div_le_div_of_nonneg_right
          (by nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1000)
            (Real.exp_pos 6).le) (pow_nonneg hy0 7)])
          (pow_nonneg hu_nonneg 8)
  have hgeom_series :
      q ^ 3 * (1 - geom)⁻¹ - P3 =
        (q ^ 3 - (w ^ 3 + (3 / 2 : ℂ) * w ^ 4 +
          (5 / 4 : ℂ) * w ^ 5 + (3 / 4 : ℂ) * w ^ 6)) +
        c * (q ^ 4 - (w ^ 4 + 2 * w ^ 5 + (13 / 6 : ℂ) * w ^ 6)) +
        c ^ 2 * (q ^ 5 - (w ^ 5 + (5 / 2 : ℂ) * w ^ 6)) +
        c ^ 3 * (q ^ 6 - w ^ 6) +
        c ^ 4 * q ^ 7 * (1 - geom)⁻¹ := by
    have hgeom_cq : geom = c * q := by
      dsimp [geom, c]
      field_simp [hu_ne]
    have hcq_ne : (1 : ℂ) - c * q ≠ 0 := by
      simpa [hgeom_cq] using hgeom_ne
    let g : ℂ := c * q
    have hg_ne : (1 : ℂ) - g ≠ 0 := by
      simpa [g] using hcq_ne
    have hginv :
        (1 - g)⁻¹ = 1 + g + g ^ 2 + g ^ 3 + g ^ 4 * (1 - g)⁻¹ := by
      field_simp [hg_ne]
      ring
    calc
      q ^ 3 * (1 - geom)⁻¹ - P3 =
          q ^ 3 * (1 - c * q)⁻¹ - P3 := by rw [hgeom_cq]
      _ = q ^ 3 * (1 + g + g ^ 2 + g ^ 3 + g ^ 4 * (1 - g)⁻¹) - P3 := by
          have hginv' :
              (1 - c * q)⁻¹ =
                1 + c * q + (c * q) ^ 2 + (c * q) ^ 3 +
                  (c * q) ^ 4 * (1 - c * q)⁻¹ := by
            simpa [g] using hginv
          change q ^ 3 * (1 - c * q)⁻¹ - P3 =
            q ^ 3 * (1 + c * q + (c * q) ^ 2 + (c * q) ^ 3 +
              (c * q) ^ 4 * (1 - c * q)⁻¹) - P3
          exact congrArg (fun z : ℂ => q ^ 3 * z - P3) hginv'
      _ =
        (q ^ 3 - (w ^ 3 + (3 / 2 : ℂ) * w ^ 4 +
          (5 / 4 : ℂ) * w ^ 5 + (3 / 4 : ℂ) * w ^ 6)) +
        c * (q ^ 4 - (w ^ 4 + 2 * w ^ 5 + (13 / 6 : ℂ) * w ^ 6)) +
        c ^ 2 * (q ^ 5 - (w ^ 5 + (5 / 2 : ℂ) * w ^ 6)) +
        c ^ 3 * (q ^ 6 - w ^ 6) +
        c ^ 4 * q ^ 7 * (1 - geom)⁻¹ := by
          rw [hgeom_cq]
          dsimp [P3, g]
          ring
  have hc_le : ‖c‖ ≤ 1 / uR := by
    rw [hc_norm]
    exact div_le_div_of_nonneg_right hrle hu_nonneg
  have hD_le : ‖D‖ ≤ 1 / uR ^ 4 := by
    rw [hD_norm]
    have hr3le : r ^ 3 ≤ 1 := by
      nlinarith [hr0, hrle, sq_nonneg r, sq_nonneg (1 - r)]
    exact div_le_div_of_nonneg_right hr3le (pow_nonneg hu_nonneg 4)
  have hDbracket :
      ‖D * (q ^ 3 * (1 - geom)⁻¹ - P3)‖
        ≤ 100000000 * Real.exp 6 * y ^ 7 / uR ^ 8 := by
    have htail :
        ‖c ^ 4 * q ^ 7 * (1 - geom)⁻¹‖
          ≤ 1000 * y ^ 7 / uR ^ 4 := by
      rw [norm_mul, norm_mul, norm_pow, norm_pow]
      have hc4 : ‖c‖ ^ 4 ≤ (1 / uR) ^ 4 :=
        pow_le_pow_left₀ (norm_nonneg c) hc_le 4
      have hq7 : ‖q‖ ^ 7 ≤ (2 * y) ^ 7 :=
        pow_le_pow_left₀ (norm_nonneg q) hq_norm 7
      calc
        ‖c‖ ^ 4 * ‖q‖ ^ 7 * ‖(1 - geom)⁻¹‖
            ≤ (1 / uR) ^ 4 * (2 * y) ^ 7 * 2 := by
          exact mul_le_mul (mul_le_mul hc4 hq7 (pow_nonneg (norm_nonneg q) 7)
            (pow_nonneg (by positivity) 4)) hinv_geom_norm (norm_nonneg _) (by positivity)
        _ = 256 * y ^ 7 / uR ^ 4 := by field_simp [huR_ne]; ring
        _ ≤ 1000 * y ^ 7 / uR ^ 4 := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right (by norm_num : (256 : ℝ) ≤ 1000)
              (pow_nonneg hy0 7))
            (pow_nonneg hu_nonneg 4)
    have hbr :
        ‖q ^ 3 * (1 - geom)⁻¹ - P3‖
          ≤ 10000000 * Real.exp 6 * y ^ 7 / uR ^ 4 := by
      rw [hgeom_series]
      calc
        ‖(q ^ 3 - (w ^ 3 + (3 / 2 : ℂ) * w ^ 4 +
            (5 / 4 : ℂ) * w ^ 5 + (3 / 4 : ℂ) * w ^ 6)) +
          c * (q ^ 4 - (w ^ 4 + 2 * w ^ 5 + (13 / 6 : ℂ) * w ^ 6)) +
          c ^ 2 * (q ^ 5 - (w ^ 5 + (5 / 2 : ℂ) * w ^ 6)) +
          c ^ 3 * (q ^ 6 - w ^ 6) +
          c ^ 4 * q ^ 7 * (1 - geom)⁻¹‖
            ≤
          ‖q ^ 3 - (w ^ 3 + (3 / 2 : ℂ) * w ^ 4 +
            (5 / 4 : ℂ) * w ^ 5 + (3 / 4 : ℂ) * w ^ 6)‖ +
          ‖c * (q ^ 4 - (w ^ 4 + 2 * w ^ 5 + (13 / 6 : ℂ) * w ^ 6))‖ +
          ‖c ^ 2 * (q ^ 5 - (w ^ 5 + (5 / 2 : ℂ) * w ^ 6))‖ +
          ‖c ^ 3 * (q ^ 6 - w ^ 6)‖ +
          ‖c ^ 4 * q ^ 7 * (1 - geom)⁻¹‖ :=
            complex_norm_add5_le _ _ _ _ _
        _ ≤ 10000 * Real.exp 6 * y ^ 7 +
            (1 / uR) * (100000 * Real.exp 6 * y ^ 7) +
            (1 / uR) ^ 2 * (500000 * Real.exp 6 * y ^ 7) +
            (1 / uR) ^ 3 * (2000000 * Real.exp 6 * y ^ 7) +
            1000 * y ^ 7 / uR ^ 4 := by
          rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow]
          exact add_le_add (add_le_add (add_le_add (add_le_add hR3
            (mul_le_mul hc_le hR4 (norm_nonneg _) (by positivity)))
            (mul_le_mul (pow_le_pow_left₀ (norm_nonneg c) hc_le 2) hR5
              (norm_nonneg _) (by positivity)))
            (mul_le_mul (pow_le_pow_left₀ (norm_nonneg c) hc_le 3) hR6
              (norm_nonneg _) (by positivity))) htail
        _ ≤ 10000000 * Real.exp 6 * y ^ 7 / uR ^ 4 := by
          let C : ℝ := Real.exp 6 * y ^ 7
          have hbase : 0 ≤ C := by
            dsimp [C]
            exact mul_nonneg (Real.exp_pos 6).le (pow_nonneg hy0 7)
          have hEge1 : 1 ≤ Real.exp 6 := by
            calc
              (1 : ℝ) = Real.exp 0 := by rw [Real.exp_zero]
              _ ≤ Real.exp 6 := Real.exp_le_exp.mpr (by norm_num)
          have hpow_le4 {k : ℕ} (hk : k ≤ 4) :
              uR ^ 4 ≤ uR ^ k := by
            have hsplit : uR ^ 4 = uR ^ k * uR ^ (4 - k) := by
              rw [← pow_add, Nat.add_sub_of_le hk]
            rw [hsplit]
            have hpow_nonneg : 0 ≤ uR ^ k := pow_nonneg hu_nonneg k
            have hrest_le_one : uR ^ (4 - k) ≤ 1 := by
              calc
                uR ^ (4 - k) ≤ 1 ^ (4 - k) :=
                  pow_le_pow_left₀ hu_nonneg hu_le_one _
                _ = 1 := by simp
            exact mul_le_of_le_one_right hpow_nonneg hrest_le_one
          have hden4_pos : 0 < uR ^ 4 := by positivity
          have hdiv_le4 {k : ℕ} (hk : k ≤ 4) {D0 : ℝ} (hD0 : 0 ≤ D0) :
              D0 / uR ^ k ≤ D0 / uR ^ 4 :=
            div_le_div_of_nonneg_left hD0 hden4_pos (hpow_le4 hk)
          have h1 :
              10000 * C ≤ 10000 * C / uR ^ 4 := by
            simpa using hdiv_le4 (by norm_num : 0 ≤ 4)
              (D0 := 10000 * C)
              (mul_nonneg (by norm_num) hbase)
          have h2 :
              (1 / uR) * (100000 * C) ≤ 100000 * C / uR ^ 4 := by
            calc
              (1 / uR) * (100000 * C) = (100000 * C) / uR ^ 1 := by
                field_simp [huR_ne]
              _ ≤ 100000 * C / uR ^ 4 :=
                hdiv_le4 (by norm_num : 1 ≤ 4)
                  (mul_nonneg (by norm_num) hbase)
          have h3 :
              (1 / uR) ^ 2 * (500000 * C) ≤ 500000 * C / uR ^ 4 := by
            calc
              (1 / uR) ^ 2 * (500000 * C) = (500000 * C) / uR ^ 2 := by
                field_simp [huR_ne]
              _ ≤ 500000 * C / uR ^ 4 :=
                hdiv_le4 (by norm_num : 2 ≤ 4)
                  (mul_nonneg (by norm_num) hbase)
          have h4 :
              (1 / uR) ^ 3 * (2000000 * C) ≤ 2000000 * C / uR ^ 4 := by
            calc
              (1 / uR) ^ 3 * (2000000 * C) = (2000000 * C) / uR ^ 3 := by
                field_simp [huR_ne]
              _ ≤ 2000000 * C / uR ^ 4 :=
                hdiv_le4 (by norm_num : 3 ≤ 4)
                  (mul_nonneg (by norm_num) hbase)
          have hyC : y ^ 7 ≤ C := by
            dsimp [C]
            calc
              y ^ 7 = 1 * y ^ 7 := by ring
              _ ≤ Real.exp 6 * y ^ 7 :=
                mul_le_mul_of_nonneg_right hEge1 (pow_nonneg hy0 7)
          have h5 :
              1000 * y ^ 7 / uR ^ 4 ≤ 1000 * C / uR ^ 4 :=
            div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hyC (by norm_num))
              (pow_nonneg hu_nonneg 4)
          have hsum :
              10000 * C +
                (1 / uR) * (100000 * C) +
                (1 / uR) ^ 2 * (500000 * C) +
                (1 / uR) ^ 3 * (2000000 * C) +
                1000 * y ^ 7 / uR ^ 4 ≤
              10000 * C / uR ^ 4 +
                100000 * C / uR ^ 4 +
                500000 * C / uR ^ 4 +
                2000000 * C / uR ^ 4 +
                1000 * C / uR ^ 4 := by
            nlinarith [h1, h2, h3, h4, h5]
          have hdenAtom :
              0 ≤ C / uR ^ 4 := div_nonneg hbase (pow_nonneg hu_nonneg 4)
          calc
            10000 * Real.exp 6 * y ^ 7 +
                (1 / uR) * (100000 * Real.exp 6 * y ^ 7) +
                (1 / uR) ^ 2 * (500000 * Real.exp 6 * y ^ 7) +
                (1 / uR) ^ 3 * (2000000 * Real.exp 6 * y ^ 7) +
                1000 * y ^ 7 / uR ^ 4
                =
              10000 * C +
                (1 / uR) * (100000 * C) +
                (1 / uR) ^ 2 * (500000 * C) +
                (1 / uR) ^ 3 * (2000000 * C) +
                1000 * y ^ 7 / uR ^ 4 := by
                  dsimp [C]
                  ring
            _ ≤ 10000 * C / uR ^ 4 +
                100000 * C / uR ^ 4 +
                500000 * C / uR ^ 4 +
                2000000 * C / uR ^ 4 +
                1000 * C / uR ^ 4 := hsum
            _ ≤ 10000000 * C / uR ^ 4 := by
              calc
                10000 * C / uR ^ 4 + 100000 * C / uR ^ 4 +
                    500000 * C / uR ^ 4 + 2000000 * C / uR ^ 4 +
                    1000 * C / uR ^ 4
                    =
                  (2611000 : ℝ) * (C / uR ^ 4) := by ring
                _ ≤ 10000000 * (C / uR ^ 4) :=
                  mul_le_mul_of_nonneg_right (by norm_num) hdenAtom
                _ = 10000000 * C / uR ^ 4 := by ring
            _ = 10000000 * Real.exp 6 * y ^ 7 / uR ^ 4 := by
              dsimp [C]
              ring
    calc
      ‖D * (q ^ 3 * (1 - geom)⁻¹ - P3)‖ =
          ‖D‖ * ‖q ^ 3 * (1 - geom)⁻¹ - P3‖ := norm_mul _ _
      _ ≤ (1 / uR ^ 4) * (10000000 * Real.exp 6 * y ^ 7 / uR ^ 4) :=
        mul_le_mul hD_le hbr (norm_nonneg _) (by positivity)
      _ = 10000000 * Real.exp 6 * y ^ 7 / uR ^ 8 := by
        field_simp [huR_ne]
      _ ≤ 100000000 * Real.exp 6 * y ^ 7 / uR ^ 8 := by
        exact div_le_div_of_nonneg_right
          (by nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 10000000)
            (Real.exp_pos 6).le) (pow_nonneg hy0 7)])
          (pow_nonneg hu_nonneg 8)
  have hmain_eq :
      fragPermLocalExponent r θ - P =
        A * (ExpStirling.expLocalRemainder θ - P1) +
          B * ((q ^ 2 - w ^ 2) - P2) +
            D * (q ^ 3 * (1 - geom)⁻¹ - P3) := by
    rw [hdecomp, hP_decomp]
    ring
  rw [show fragPermLocalExponent r θ -
        (-Complex.I * ((fragPermSaddleB3Real r : ℂ) / 6) * (θ : ℂ) ^ 3 +
          ((fragPermSaddleB4Real r : ℂ) / 24) * (θ : ℂ) ^ 4 +
          Complex.I * ((fragPermSaddleB5Real r : ℂ) / 120) * (θ : ℂ) ^ 5 -
          ((fragPermSaddleB6Real r : ℂ) / 720) * (θ : ℂ) ^ 6) =
        fragPermLocalExponent r θ - P by rfl]
  rw [hmain_eq]
  calc
    ‖A * (ExpStirling.expLocalRemainder θ - P1) +
          B * ((q ^ 2 - w ^ 2) - P2) +
            D * (q ^ 3 * (1 - geom)⁻¹ - P3)‖
        ≤ ‖A * (ExpStirling.expLocalRemainder θ - P1)‖ +
            ‖B * ((q ^ 2 - w ^ 2) - P2)‖ +
            ‖D * (q ^ 3 * (1 - geom)⁻¹ - P3)‖ := by
          calc
            ‖A * (ExpStirling.expLocalRemainder θ - P1) +
                B * ((q ^ 2 - w ^ 2) - P2) +
                  D * (q ^ 3 * (1 - geom)⁻¹ - P3)‖
                ≤ ‖A * (ExpStirling.expLocalRemainder θ - P1) +
                    B * ((q ^ 2 - w ^ 2) - P2)‖ +
                    ‖D * (q ^ 3 * (1 - geom)⁻¹ - P3)‖ := norm_add_le _ _
            _ ≤ (‖A * (ExpStirling.expLocalRemainder θ - P1)‖ +
                  ‖B * ((q ^ 2 - w ^ 2) - P2)‖) +
                    ‖D * (q ^ 3 * (1 - geom)⁻¹ - P3)‖ := by
                have hAB :
                    ‖A * (ExpStirling.expLocalRemainder θ - P1) +
                      B * ((q ^ 2 - w ^ 2) - P2)‖ ≤
                    ‖A * (ExpStirling.expLocalRemainder θ - P1)‖ +
                      ‖B * ((q ^ 2 - w ^ 2) - P2)‖ :=
                  norm_add_le _ _
                exact add_le_add_left hAB _
            _ = ‖A * (ExpStirling.expLocalRemainder θ - P1)‖ +
                ‖B * ((q ^ 2 - w ^ 2) - P2)‖ +
                  ‖D * (q ^ 3 * (1 - geom)⁻¹ - P3)‖ := by rfl
    _ ≤ 1000 * Real.exp 6 * y ^ 7 / uR ^ 8 +
          1000000 * Real.exp 6 * y ^ 7 / uR ^ 8 +
            100000000 * Real.exp 6 * y ^ 7 / uR ^ 8 := by
        exact add_le_add (add_le_add hAterm hBterm) hDbracket
    _ ≤ 1000000000 * Real.exp 6 * |θ| ^ 7 / (1 - r) ^ 8 := by
        let Z : ℝ := Real.exp 6 * |θ| ^ 7 / (1 - r) ^ 8
        have hden_nonneg : 0 ≤ (1 - r) ^ 8 := by positivity
        have hCnon : 0 ≤ Real.exp 6 * |θ| ^ 7 :=
          mul_nonneg (Real.exp_pos 6).le (pow_nonneg (abs_nonneg θ) 7)
        have hZ : 0 ≤ Z := by
          dsimp [Z]
          exact div_nonneg hCnon hden_nonneg
        calc
          1000 * Real.exp 6 * y ^ 7 / uR ^ 8 +
              1000000 * Real.exp 6 * y ^ 7 / uR ^ 8 +
              100000000 * Real.exp 6 * y ^ 7 / uR ^ 8
              =
            (101001000 : ℝ) * Z := by
              dsimp [Z, y, uR]
              ring
          _ ≤ 1000000000 * Z :=
            mul_le_mul_of_nonneg_right (by norm_num) hZ
          _ = 1000000000 * Real.exp 6 * |θ| ^ 7 / (1 - r) ^ 8 := by
            dsimp [Z]
            ring

private def fragPermThirdScaledRemainderConst : ℝ :=
  200000000000 * Real.exp 6

private lemma fragPermThirdScaledRemainderConst_pos :
    0 < fragPermThirdScaledRemainderConst := by
  unfold fragPermThirdScaledRemainderConst
  positivity

private lemma fragPerm_rpow_calc_five_halves {u : ℝ} (hu : 0 < u) :
    (1 / u ^ 8) * (2 * u ^ (3 / 2 : ℝ)) ^ 7 =
      128 * u ^ (5 / 2 : ℝ) := by
  have hun : 0 ≤ u := hu.le
  have hpow :
      (u ^ (3 / 2 : ℝ)) ^ 7 = u ^ (21 / 2 : ℝ) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hun]
    norm_num
  calc
    (1 / u ^ 8) * (2 * u ^ (3 / 2 : ℝ)) ^ 7
        = 128 * (u ^ (21 / 2 : ℝ) / u ^ 8) := by
          rw [mul_pow, hpow]
          ring
    _ = 128 * u ^ (5 / 2 : ℝ) := by
      rw [show u ^ 8 = u ^ (8 : ℝ) by exact (Real.rpow_natCast u 8).symm]
      rw [div_eq_mul_inv]
      rw [← Real.rpow_neg hun (8 : ℝ)]
      rw [← Real.rpow_add hu]
      norm_num

private lemma fragPermThirdScaledRemainder_norm_le {r x : ℝ}
    (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1)
    (hθδ : |x / Real.sqrt (fragPermSaddleBReal r)| ≤ fragPermThirdSaddleDeltaReal r)
    (hδle : fragPermThirdSaddleDeltaReal r ≤ 1)
    (hδu : fragPermThirdSaddleDeltaReal r ≤ (1 - r) / 4) :
    ‖fragPermThirdScaledRemainder r x‖ ≤
      fragPermThirdScaledRemainderConst * (1 - r) ^ (5 / 2 : ℝ) * |x| ^ 7 := by
  let u : ℝ := 1 - r
  have hu_pos : 0 < u := by dsimp [u]; linarith [hr.2]
  have hu_nonneg : 0 ≤ u := hu_pos.le
  have hbpos : 0 < fragPermSaddleBReal r := by
    unfold fragPermSaddleBReal
    have hrpos : 0 < r := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hr.1
    have hnum : 0 < r * (1 + r) := by positivity
    have hden : 0 < (1 - r) ^ 3 := by positivity
    exact div_pos hnum hden
  have hsqrt_pos : 0 < Real.sqrt (fragPermSaddleBReal r) := Real.sqrt_pos.mpr hbpos
  have hrem := fragPermLocalExponent_seventh_remainder_norm_le
    (r := r) (θ := x / Real.sqrt (fragPermSaddleBReal r)) hr hθδ hδle hδu
  rw [fragPermThirdScaledRemainder_eq_unscaled hbpos]
  have hsqrt_lower :
      (1 / 2 : ℝ) * u ^ (-(3 / 2 : ℝ)) ≤
        Real.sqrt (fragPermSaddleBReal r) := by
    simpa [u] using fragPerm_sqrt_b_lower_of_Ioo_half_one hr
  have hlower_pos : 0 < (1 / 2 : ℝ) * u ^ (-(3 / 2 : ℝ)) := by
    positivity
  have hupow_pos : 0 < u ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hu_pos _
  have hθ_abs_le :
      |x / Real.sqrt (fragPermSaddleBReal r)| ≤
        2 * u ^ (3 / 2 : ℝ) * |x| := by
    rw [abs_div, abs_of_pos hsqrt_pos]
    calc
      |x| / Real.sqrt (fragPermSaddleBReal r) ≤
          |x| / ((1 / 2 : ℝ) * u ^ (-(3 / 2 : ℝ))) :=
            div_le_div_of_nonneg_left (abs_nonneg x) hlower_pos hsqrt_lower
      _ = 2 * u ^ (3 / 2 : ℝ) * |x| := by
        rw [Real.rpow_neg hu_nonneg (3 / 2 : ℝ)]
        field_simp [hupow_pos.ne']
  have hθ7_le :
      |x / Real.sqrt (fragPermSaddleBReal r)| ^ 7 ≤
        (2 * u ^ (3 / 2 : ℝ) * |x|) ^ 7 :=
    pow_le_pow_left₀ (abs_nonneg _) hθ_abs_le 7
  have hscale :
      (2 * u ^ (3 / 2 : ℝ) * |x|) ^ 7 / u ^ 8 =
        128 * u ^ (5 / 2 : ℝ) * |x| ^ 7 := by
    calc
      (2 * u ^ (3 / 2 : ℝ) * |x|) ^ 7 / u ^ 8 =
          ((2 * u ^ (3 / 2 : ℝ)) ^ 7 / u ^ 8) * |x| ^ 7 := by ring
      _ = ((1 / u ^ 8) * (2 * u ^ (3 / 2 : ℝ)) ^ 7) * |x| ^ 7 := by ring
      _ = 128 * u ^ (5 / 2 : ℝ) * |x| ^ 7 := by
        rw [fragPerm_rpow_calc_five_halves hu_pos]
  have hconst_nonneg : 0 ≤ 1000000000 * Real.exp 6 :=
    mul_nonneg (by norm_num) (Real.exp_pos 6).le
  have hu8_nonneg : 0 ≤ u ^ 8 := pow_nonneg hu_nonneg 8
  calc
    ‖fragPermLocalExponent r (x / Real.sqrt (fragPermSaddleBReal r)) -
        (-Complex.I * ((fragPermSaddleB3Real r : ℂ) / 6) *
            ((x / Real.sqrt (fragPermSaddleBReal r) : ℝ) : ℂ) ^ 3 +
          ((fragPermSaddleB4Real r : ℂ) / 24) *
            ((x / Real.sqrt (fragPermSaddleBReal r) : ℝ) : ℂ) ^ 4 +
          Complex.I * ((fragPermSaddleB5Real r : ℂ) / 120) *
            ((x / Real.sqrt (fragPermSaddleBReal r) : ℝ) : ℂ) ^ 5 -
          ((fragPermSaddleB6Real r : ℂ) / 720) *
            ((x / Real.sqrt (fragPermSaddleBReal r) : ℝ) : ℂ) ^ 6)‖
        ≤ 1000000000 * Real.exp 6 *
            |x / Real.sqrt (fragPermSaddleBReal r)| ^ 7 / (1 - r) ^ 8 := hrem
    _ ≤ 1000000000 * Real.exp 6 *
          (2 * u ^ (3 / 2 : ℝ) * |x|) ^ 7 / u ^ 8 := by
        dsimp [u]
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hθ7_le hconst_nonneg) hu8_nonneg
    _ = 1000000000 * Real.exp 6 *
          ((2 * u ^ (3 / 2 : ℝ) * |x|) ^ 7 / u ^ 8) := by ring
    _ = 1000000000 * Real.exp 6 *
          (128 * u ^ (5 / 2 : ℝ) * |x| ^ 7) := by rw [hscale]
    _ ≤ fragPermThirdScaledRemainderConst * u ^ (5 / 2 : ℝ) * |x| ^ 7 := by
      unfold fragPermThirdScaledRemainderConst
      have htail_nonneg : 0 ≤ u ^ (5 / 2 : ℝ) * |x| ^ 7 := by positivity
      calc
        1000000000 * Real.exp 6 *
            (128 * u ^ (5 / 2 : ℝ) * |x| ^ 7)
            = (128000000000 * Real.exp 6) *
                (u ^ (5 / 2 : ℝ) * |x| ^ 7) := by ring
        _ ≤ (200000000000 * Real.exp 6) *
              (u ^ (5 / 2 : ℝ) * |x| ^ 7) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (by norm_num) (Real.exp_pos 6).le)
            htail_nonneg
        _ = (200000000000 * Real.exp 6) * u ^ (5 / 2 : ℝ) * |x| ^ 7 := by ring
    _ = fragPermThirdScaledRemainderConst * (1 - r) ^ (5 / 2 : ℝ) * |x| ^ 7 := by
      dsimp [u]

private def fragPermThirdLocalL1Const : ℝ :=
  100000 * (Real.exp 1 + 1) *
    ((100 + fragPermThirdScaledRemainderConst) ^ 5 +
      (100 + fragPermThirdScaledRemainderConst) ^ 4 +
      (100 + fragPermThirdScaledRemainderConst) ^ 3 +
      (100 + fragPermThirdScaledRemainderConst) ^ 2 +
      (100 + fragPermThirdScaledRemainderConst) + 1)

private lemma fragPermThirdLocalL1Const_pos : 0 < fragPermThirdLocalL1Const := by
  unfold fragPermThirdLocalL1Const fragPermThirdScaledRemainderConst
  positivity

private lemma fragPermThirdLocal_poly_bound {y : ℝ} (hy0 : 0 ≤ y) :
    let K : ℝ := fragPermThirdScaledRemainderConst
    let S1 : ℝ := 10 * y ^ 3 + 10 * y ^ 4 + 40 * y ^ 5 + 10 * y ^ 6 + K * y ^ 7
    let S2 : ℝ := 10 * y ^ 4 + 40 * y ^ 5 + 10 * y ^ 6 + K * y ^ 7
    let S3 : ℝ := 10 * y ^ 6 + K * y ^ 7
    let S4 : ℝ := 40 * y ^ 5 + 10 * y ^ 6 + K * y ^ 7
    let G : ℝ := ∑ k ∈ Finset.range 36, y ^ k
    Real.exp 1 * S1 ^ 5 + K * y ^ 7 +
      (1600 * y ^ 10 + 800 * y ^ 9 + 2 * S1 * S3 + S3 ^ 2) +
      (3 * (10 * y ^ 3) ^ 2 * S4 + 3 * (10 * y ^ 3) * S2 ^ 2 + S2 ^ 3) +
      S2 * (S1 ^ 3 + S1 ^ 2 * (10 * y ^ 3) +
        S1 * (10 * y ^ 3) ^ 2 + (10 * y ^ 3) ^ 3)
        ≤ fragPermThirdLocalL1Const * G := by
  intro K S1 S2 S3 S4 G
  let B0 : ℝ := y ^ 3 + y ^ 4 + y ^ 5 + y ^ 6 + y ^ 7
  let L : ℝ := 100 + K
  have hK : 0 ≤ K := by
    dsimp [K]
    exact fragPermThirdScaledRemainderConst_pos.le
  have hE1 : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
  have hB0_nonneg : 0 ≤ B0 := by dsimp [B0]; positivity
  have hL_nonneg : 0 ≤ L := by dsimp [L]; positivity
  have hL_ge_one : 1 ≤ L := by dsimp [L]; nlinarith [hK]
  have hLsum_nonneg :
      0 ≤ L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1 := by positivity
  have hG_nonneg : 0 ≤ G := by
    dsimp [G]
    exact Finset.sum_nonneg fun k hk => pow_nonneg hy0 k
  have hpow_le_G : ∀ {m : ℕ}, m < 36 → y ^ m ≤ G := by
    intro m hm
    dsimp [G]
    exact Finset.single_le_sum (fun k hk => pow_nonneg hy0 k)
      (Finset.mem_range.mpr hm)
  have hG_ge_one : 1 ≤ G := by
    simpa using (hpow_le_G (m := 0) (by norm_num))
  have hB0_le_five_of_le_one (hy1 : y ≤ 1) : B0 ≤ 5 := by
    dsimp [B0]
    have h3 : y ^ 3 ≤ 1 := by simpa using (pow_le_one₀ (n := 3) hy0 hy1)
    have h4 : y ^ 4 ≤ 1 := by simpa using (pow_le_one₀ (n := 4) hy0 hy1)
    have h5 : y ^ 5 ≤ 1 := by simpa using (pow_le_one₀ (n := 5) hy0 hy1)
    have h6 : y ^ 6 ≤ 1 := by simpa using (pow_le_one₀ (n := 6) hy0 hy1)
    have h7 : y ^ 7 ≤ 1 := by simpa using (pow_le_one₀ (n := 7) hy0 hy1)
    nlinarith
  have hB0_le_five_y7_of_ge_one (hy1 : 1 ≤ y) : B0 ≤ 5 * y ^ 7 := by
    dsimp [B0]
    have h3 : y ^ 3 ≤ y ^ 7 := pow_le_pow_right₀ hy1 (by norm_num)
    have h4 : y ^ 4 ≤ y ^ 7 := pow_le_pow_right₀ hy1 (by norm_num)
    have h5 : y ^ 5 ≤ y ^ 7 := pow_le_pow_right₀ hy1 (by norm_num)
    have h6 : y ^ 6 ≤ y ^ 7 := pow_le_pow_right₀ hy1 (by norm_num)
    nlinarith
  have hB1 : B0 ≤ 5 * G := by
    by_cases hy1 : y ≤ 1
    · calc
        B0 ≤ 5 := hB0_le_five_of_le_one hy1
        _ ≤ 5 * G := by nlinarith [hG_ge_one]
    · have hyge : 1 ≤ y := by linarith
      calc
        B0 ≤ 5 * y ^ 7 := hB0_le_five_y7_of_ge_one hyge
        _ ≤ 5 * G := by
          exact mul_le_mul_of_nonneg_left
            (hpow_le_G (m := 7) (by norm_num)) (by norm_num)
  have hB2 : B0 ^ 2 ≤ 25 * G := by
    by_cases hy1 : y ≤ 1
    · calc
        B0 ^ 2 ≤ 5 ^ 2 := pow_le_pow_left₀ hB0_nonneg (hB0_le_five_of_le_one hy1) 2
        _ = (25 : ℝ) := by norm_num
        _ ≤ 25 * G := by nlinarith [hG_ge_one]
    · have hyge : 1 ≤ y := by linarith
      calc
        B0 ^ 2 ≤ (5 * y ^ 7) ^ 2 :=
          pow_le_pow_left₀ hB0_nonneg (hB0_le_five_y7_of_ge_one hyge) 2
        _ = 25 * y ^ 14 := by ring
        _ ≤ 25 * G :=
          mul_le_mul_of_nonneg_left (hpow_le_G (m := 14) (by norm_num))
            (by norm_num)
  have hB3 : B0 ^ 3 ≤ 125 * G := by
    by_cases hy1 : y ≤ 1
    · calc
        B0 ^ 3 ≤ 5 ^ 3 := pow_le_pow_left₀ hB0_nonneg (hB0_le_five_of_le_one hy1) 3
        _ = (125 : ℝ) := by norm_num
        _ ≤ 125 * G := by nlinarith [hG_ge_one]
    · have hyge : 1 ≤ y := by linarith
      calc
        B0 ^ 3 ≤ (5 * y ^ 7) ^ 3 :=
          pow_le_pow_left₀ hB0_nonneg (hB0_le_five_y7_of_ge_one hyge) 3
        _ = 125 * y ^ 21 := by ring
        _ ≤ 125 * G :=
          mul_le_mul_of_nonneg_left (hpow_le_G (m := 21) (by norm_num))
            (by norm_num)
  have hB4 : B0 ^ 4 ≤ 625 * G := by
    by_cases hy1 : y ≤ 1
    · calc
        B0 ^ 4 ≤ 5 ^ 4 := pow_le_pow_left₀ hB0_nonneg (hB0_le_five_of_le_one hy1) 4
        _ = (625 : ℝ) := by norm_num
        _ ≤ 625 * G := by nlinarith [hG_ge_one]
    · have hyge : 1 ≤ y := by linarith
      calc
        B0 ^ 4 ≤ (5 * y ^ 7) ^ 4 :=
          pow_le_pow_left₀ hB0_nonneg (hB0_le_five_y7_of_ge_one hyge) 4
        _ = 625 * y ^ 28 := by ring
        _ ≤ 625 * G :=
          mul_le_mul_of_nonneg_left (hpow_le_G (m := 28) (by norm_num))
            (by norm_num)
  have hB5 : B0 ^ 5 ≤ 3125 * G := by
    by_cases hy1 : y ≤ 1
    · calc
        B0 ^ 5 ≤ 5 ^ 5 := pow_le_pow_left₀ hB0_nonneg (hB0_le_five_of_le_one hy1) 5
        _ = (3125 : ℝ) := by norm_num
        _ ≤ 3125 * G := by nlinarith [hG_ge_one]
    · have hyge : 1 ≤ y := by linarith
      calc
        B0 ^ 5 ≤ (5 * y ^ 7) ^ 5 :=
          pow_le_pow_left₀ hB0_nonneg (hB0_le_five_y7_of_ge_one hyge) 5
        _ = 3125 * y ^ 35 := by ring
        _ ≤ 3125 * G :=
          mul_le_mul_of_nonneg_left (hpow_le_G (m := 35) (by norm_num))
            (by norm_num)
  have hLsum_ge1 : 1 ≤ L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1 := by
    nlinarith [pow_nonneg hL_nonneg 2, pow_nonneg hL_nonneg 3,
      pow_nonneg hL_nonneg 4, pow_nonneg hL_nonneg 5, hL_nonneg]
  have hLpow2 : L ^ 2 ≤ L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1 := by
    nlinarith [pow_nonneg hL_nonneg 3, pow_nonneg hL_nonneg 4,
      pow_nonneg hL_nonneg 5, hL_nonneg]
  have hLpow3 : L ^ 3 ≤ L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1 := by
    nlinarith [pow_nonneg hL_nonneg 2, pow_nonneg hL_nonneg 4,
      pow_nonneg hL_nonneg 5, hL_nonneg]
  have hLpow4 : L ^ 4 ≤ L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1 := by
    nlinarith [pow_nonneg hL_nonneg 2, pow_nonneg hL_nonneg 3,
      pow_nonneg hL_nonneg 5, hL_nonneg]
  have hLpow5 : L ^ 5 ≤ L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1 := by
    nlinarith [pow_nonneg hL_nonneg 2, pow_nonneg hL_nonneg 3,
      pow_nonneg hL_nonneg 4, hL_nonneg]
  have hS1 : S1 ≤ L * B0 := by
    dsimp [S1, L, B0]
    nlinarith [hK, pow_nonneg hy0 3, pow_nonneg hy0 4, pow_nonneg hy0 5,
      pow_nonneg hy0 6, pow_nonneg hy0 7]
  have hS2 : S2 ≤ L * B0 := by
    dsimp [S2, L, B0]
    nlinarith [hK, pow_nonneg hy0 3, pow_nonneg hy0 4, pow_nonneg hy0 5,
      pow_nonneg hy0 6, pow_nonneg hy0 7]
  have hS3 : S3 ≤ L * B0 := by
    dsimp [S3, L, B0]
    nlinarith [hK, pow_nonneg hy0 3, pow_nonneg hy0 4, pow_nonneg hy0 5,
      pow_nonneg hy0 6, pow_nonneg hy0 7]
  have hS4 : S4 ≤ L * B0 := by
    dsimp [S4, L, B0]
    nlinarith [hK, pow_nonneg hy0 3, pow_nonneg hy0 4, pow_nonneg hy0 5,
      pow_nonneg hy0 6, pow_nonneg hy0 7]
  have hT : 10 * y ^ 3 ≤ L * B0 := by
    dsimp [L, B0]
    nlinarith [hK, pow_nonneg hy0 3, pow_nonneg hy0 4, pow_nonneg hy0 5,
      pow_nonneg hy0 6, pow_nonneg hy0 7]
  have hK_le_Lsum : K ≤ L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1 := by
    dsimp [L]
    nlinarith [hK, pow_nonneg hL_nonneg 2, pow_nonneg hL_nonneg 3,
      pow_nonneg hL_nonneg 4, pow_nonneg hL_nonneg 5]
  have hS1_nonneg : 0 ≤ S1 := by dsimp [S1]; positivity
  have hS2_nonneg : 0 ≤ S2 := by dsimp [S2]; positivity
  have hS3_nonneg : 0 ≤ S3 := by dsimp [S3]; positivity
  have hS4_nonneg : 0 ≤ S4 := by dsimp [S4]; positivity
  have hT_nonneg : 0 ≤ 10 * y ^ 3 := by positivity
  have hLsumG_nonneg :
      0 ≤ (L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G :=
    mul_nonneg hLsum_nonneg hG_nonneg
  have hy7_le_G : y ^ 7 ≤ G := by
    exact hpow_le_G (m := 7) (by norm_num)
  have hy9_le_G : y ^ 9 ≤ G := by
    exact hpow_le_G (m := 9) (by norm_num)
  have hy10_le_G : y ^ 10 ≤ G := by
    exact hpow_le_G (m := 10) (by norm_num)
  have hG_le_LsumG :
      G ≤ (L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G := by
    calc
      G = 1 * G := by ring
      _ ≤ (L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G :=
        mul_le_mul_of_nonneg_right hLsum_ge1 hG_nonneg
  have hS1_5 : S1 ^ 5 ≤ L ^ 5 * B0 ^ 5 := by
    calc
      S1 ^ 5 ≤ (L * B0) ^ 5 := pow_le_pow_left₀ hS1_nonneg hS1 5
      _ = L ^ 5 * B0 ^ 5 := by ring
  have hS1S3 : S1 * S3 ≤ L ^ 2 * B0 ^ 2 := by
    calc
      S1 * S3 ≤ (L * B0) * (L * B0) :=
        mul_le_mul hS1 hS3 hS3_nonneg (mul_nonneg hL_nonneg hB0_nonneg)
      _ = L ^ 2 * B0 ^ 2 := by ring
  have hS3sq : S3 ^ 2 ≤ L ^ 2 * B0 ^ 2 := by
    calc
      S3 ^ 2 ≤ (L * B0) ^ 2 := pow_le_pow_left₀ hS3_nonneg hS3 2
      _ = L ^ 2 * B0 ^ 2 := by ring
  have hT2S4 : (10 * y ^ 3) ^ 2 * S4 ≤ L ^ 3 * B0 ^ 3 := by
    have hT2 : (10 * y ^ 3) ^ 2 ≤ (L * B0) ^ 2 :=
      pow_le_pow_left₀ hT_nonneg hT 2
    calc
      (10 * y ^ 3) ^ 2 * S4 ≤ (L * B0) ^ 2 * (L * B0) :=
        mul_le_mul hT2 hS4 hS4_nonneg (pow_nonneg (mul_nonneg hL_nonneg hB0_nonneg) 2)
      _ = L ^ 3 * B0 ^ 3 := by ring
  have hTS2sq : (10 * y ^ 3) * S2 ^ 2 ≤ L ^ 3 * B0 ^ 3 := by
    have hS2sq : S2 ^ 2 ≤ (L * B0) ^ 2 :=
      pow_le_pow_left₀ hS2_nonneg hS2 2
    calc
      (10 * y ^ 3) * S2 ^ 2 ≤ (L * B0) * (L * B0) ^ 2 :=
        mul_le_mul hT hS2sq (pow_nonneg hS2_nonneg 2) (mul_nonneg hL_nonneg hB0_nonneg)
      _ = L ^ 3 * B0 ^ 3 := by ring
  have hS2_3 : S2 ^ 3 ≤ L ^ 3 * B0 ^ 3 := by
    calc
      S2 ^ 3 ≤ (L * B0) ^ 3 := pow_le_pow_left₀ hS2_nonneg hS2 3
      _ = L ^ 3 * B0 ^ 3 := by ring
  have hfour_poly :
      S2 * (S1 ^ 3 + S1 ^ 2 * (10 * y ^ 3) +
        S1 * (10 * y ^ 3) ^ 2 + (10 * y ^ 3) ^ 3)
        ≤ 4 * L ^ 4 * B0 ^ 4 := by
    have hS1_3 : S1 ^ 3 ≤ (L * B0) ^ 3 :=
      pow_le_pow_left₀ hS1_nonneg hS1 3
    have hS1_2T : S1 ^ 2 * (10 * y ^ 3) ≤ (L * B0) ^ 3 := by
      have hS1_2 : S1 ^ 2 ≤ (L * B0) ^ 2 :=
        pow_le_pow_left₀ hS1_nonneg hS1 2
      calc
        S1 ^ 2 * (10 * y ^ 3) ≤ (L * B0) ^ 2 * (L * B0) :=
          mul_le_mul hS1_2 hT hT_nonneg (pow_nonneg (mul_nonneg hL_nonneg hB0_nonneg) 2)
        _ = (L * B0) ^ 3 := by ring
    have hS1T2 : S1 * (10 * y ^ 3) ^ 2 ≤ (L * B0) ^ 3 := by
      have hT2 : (10 * y ^ 3) ^ 2 ≤ (L * B0) ^ 2 :=
        pow_le_pow_left₀ hT_nonneg hT 2
      calc
        S1 * (10 * y ^ 3) ^ 2 ≤ (L * B0) * (L * B0) ^ 2 :=
          mul_le_mul hS1 hT2 (pow_nonneg hT_nonneg 2) (mul_nonneg hL_nonneg hB0_nonneg)
        _ = (L * B0) ^ 3 := by ring
    have hT3 : (10 * y ^ 3) ^ 3 ≤ (L * B0) ^ 3 :=
      pow_le_pow_left₀ hT_nonneg hT 3
    have hsum4 :
        S1 ^ 3 + S1 ^ 2 * (10 * y ^ 3) +
          S1 * (10 * y ^ 3) ^ 2 + (10 * y ^ 3) ^ 3
          ≤ 4 * (L * B0) ^ 3 := by
      linarith [hS1_3, hS1_2T, hS1T2, hT3]
    calc
      S2 * (S1 ^ 3 + S1 ^ 2 * (10 * y ^ 3) +
        S1 * (10 * y ^ 3) ^ 2 + (10 * y ^ 3) ^ 3)
          ≤ (L * B0) * (4 * (L * B0) ^ 3) := by
            exact mul_le_mul hS2 hsum4
              (by positivity) (mul_nonneg hL_nonneg hB0_nonneg)
      _ = 4 * L ^ 4 * B0 ^ 4 := by ring
  have hL2B2 :
      L ^ 2 * B0 ^ 2 ≤
        25 * ((L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G) := by
    calc
      L ^ 2 * B0 ^ 2 ≤
          (L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * (25 * G) :=
        mul_le_mul hLpow2 hB2 (pow_nonneg hB0_nonneg 2) hLsum_nonneg
      _ = 25 * ((L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G) := by ring
  have hL3B3 :
      L ^ 3 * B0 ^ 3 ≤
        125 * ((L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G) := by
    calc
      L ^ 3 * B0 ^ 3 ≤
          (L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * (125 * G) :=
        mul_le_mul hLpow3 hB3 (pow_nonneg hB0_nonneg 3) hLsum_nonneg
      _ = 125 * ((L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G) := by ring
  have hL4B4 :
      L ^ 4 * B0 ^ 4 ≤
        625 * ((L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G) := by
    calc
      L ^ 4 * B0 ^ 4 ≤
          (L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * (625 * G) :=
        mul_le_mul hLpow4 hB4 (pow_nonneg hB0_nonneg 4) hLsum_nonneg
      _ = 625 * ((L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G) := by ring
  have hL5B5 :
      L ^ 5 * B0 ^ 5 ≤
        3125 * ((L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G) := by
    calc
      L ^ 5 * B0 ^ 5 ≤
          (L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * (3125 * G) :=
        mul_le_mul hLpow5 hB5 (pow_nonneg hB0_nonneg 5) hLsum_nonneg
      _ = 3125 * ((L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G) := by ring
  have hpoly_to :
      Real.exp 1 * S1 ^ 5 + K * y ^ 7 +
      (1600 * y ^ 10 + 800 * y ^ 9 + 2 * S1 * S3 + S3 ^ 2) +
      (3 * (10 * y ^ 3) ^ 2 * S4 + 3 * (10 * y ^ 3) * S2 ^ 2 + S2 ^ 3) +
      S2 * (S1 ^ 3 + S1 ^ 2 * (10 * y ^ 3) +
        S1 * (10 * y ^ 3) ^ 2 + (10 * y ^ 3) ^ 3)
        ≤
      10000 * (Real.exp 1 + 1) *
        (L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G := by
    have hExp :
        Real.exp 1 * S1 ^ 5 ≤
          3125 * Real.exp 1 *
            ((L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G) := by
      calc
        Real.exp 1 * S1 ^ 5 ≤ Real.exp 1 * (L ^ 5 * B0 ^ 5) :=
          mul_le_mul_of_nonneg_left hS1_5 hE1
        _ ≤ Real.exp 1 *
              (3125 * ((L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G)) :=
          mul_le_mul_of_nonneg_left hL5B5 hE1
        _ = 3125 * Real.exp 1 *
              ((L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G) := by ring
    have hR :
        K * y ^ 7 ≤
          (L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G := by
      exact mul_le_mul hK_le_Lsum hy7_le_G (pow_nonneg hy0 7) hLsum_nonneg
    have hQuad :
        1600 * y ^ 10 + 800 * y ^ 9 + 2 * S1 * S3 + S3 ^ 2 ≤
          2475 * ((L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G) := by
      have hy10_L :
          y ^ 10 ≤ (L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G :=
        hy10_le_G.trans hG_le_LsumG
      have hy9_L :
          y ^ 9 ≤ (L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G :=
        hy9_le_G.trans hG_le_LsumG
      have hS1S3_L :
          S1 * S3 ≤ 25 *
            ((L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G) :=
        hS1S3.trans hL2B2
      have hS3sq_L :
          S3 ^ 2 ≤ 25 *
            ((L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G) :=
        hS3sq.trans hL2B2
      linarith
    have hCube :
        3 * (10 * y ^ 3) ^ 2 * S4 + 3 * (10 * y ^ 3) * S2 ^ 2 + S2 ^ 3 ≤
          875 * ((L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G) := by
      have hT2S4_L :
          (10 * y ^ 3) ^ 2 * S4 ≤ 125 *
            ((L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G) :=
        hT2S4.trans hL3B3
      have hTS2sq_L :
          (10 * y ^ 3) * S2 ^ 2 ≤ 125 *
            ((L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G) :=
        hTS2sq.trans hL3B3
      have hS2_3_L :
          S2 ^ 3 ≤ 125 *
            ((L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G) :=
        hS2_3.trans hL3B3
      linarith
    have hFourth :
        S2 * (S1 ^ 3 + S1 ^ 2 * (10 * y ^ 3) +
          S1 * (10 * y ^ 3) ^ 2 + (10 * y ^ 3) ^ 3) ≤
          2500 * ((L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G) := by
      calc
        S2 * (S1 ^ 3 + S1 ^ 2 * (10 * y ^ 3) +
            S1 * (10 * y ^ 3) ^ 2 + (10 * y ^ 3) ^ 3)
            ≤ 4 * L ^ 4 * B0 ^ 4 := hfour_poly
        _ = 4 * (L ^ 4 * B0 ^ 4) := by ring
        _ ≤ 4 *
            (625 * ((L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G)) :=
          mul_le_mul_of_nonneg_left hL4B4 (by norm_num : (0 : ℝ) ≤ 4)
        _ = 2500 * ((L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G) := by ring
    have hcoef :
        3125 * Real.exp 1 + 5851 ≤ 10000 * (Real.exp 1 + 1) := by
      linarith [hE1]
    calc
      Real.exp 1 * S1 ^ 5 + K * y ^ 7 +
        (1600 * y ^ 10 + 800 * y ^ 9 + 2 * S1 * S3 + S3 ^ 2) +
        (3 * (10 * y ^ 3) ^ 2 * S4 + 3 * (10 * y ^ 3) * S2 ^ 2 + S2 ^ 3) +
        S2 * (S1 ^ 3 + S1 ^ 2 * (10 * y ^ 3) +
          S1 * (10 * y ^ 3) ^ 2 + (10 * y ^ 3) ^ 3)
          ≤
        3125 * Real.exp 1 *
            ((L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G) +
          (L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G +
          2475 * ((L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G) +
          875 * ((L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G) +
          2500 * ((L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G) := by
            linarith
      _ = (3125 * Real.exp 1 + 5851) *
            ((L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G) := by ring
      _ ≤ (10000 * (Real.exp 1 + 1)) *
            ((L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G) := by
        exact mul_le_mul_of_nonneg_right hcoef hLsumG_nonneg
      _ = 10000 * (Real.exp 1 + 1) *
            (L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G := by
        rw [← mul_assoc]
  calc
    Real.exp 1 * S1 ^ 5 + K * y ^ 7 +
      (1600 * y ^ 10 + 800 * y ^ 9 + 2 * S1 * S3 + S3 ^ 2) +
      (3 * (10 * y ^ 3) ^ 2 * S4 + 3 * (10 * y ^ 3) * S2 ^ 2 + S2 ^ 3) +
      S2 * (S1 ^ 3 + S1 ^ 2 * (10 * y ^ 3) +
        S1 * (10 * y ^ 3) ^ 2 + (10 * y ^ 3) ^ 3)
        ≤ 10000 * (Real.exp 1 + 1) *
        (L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G := hpoly_to
    _ ≤ fragPermThirdLocalL1Const * G := by
      have hbase_nonneg :
          0 ≤ (Real.exp 1 + 1) *
              (L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G := by
        exact mul_nonneg (mul_nonneg (by positivity) hLsum_nonneg) hG_nonneg
      calc
        10000 * (Real.exp 1 + 1) *
            (L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G
            = 10000 * ((Real.exp 1 + 1) *
                (L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G) := by ring
        _ ≤ 100000 * ((Real.exp 1 + 1) *
              (L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G) :=
          mul_le_mul_of_nonneg_right (by norm_num : (10000 : ℝ) ≤ 100000)
            hbase_nonneg
        _ = fragPermThirdLocalL1Const * G := by
          dsimp [fragPermThirdLocalL1Const, L, K]
          ring

private lemma fragPerm_third_local_integrand_bound {r x : ℝ}
    (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1)
    (hθδ : |x / Real.sqrt (fragPermSaddleBReal r)| ≤ fragPermThirdSaddleDeltaReal r)
    (hδle : fragPermThirdSaddleDeltaReal r ≤ 1)
    (hδu : fragPermThirdSaddleDeltaReal r ≤ (1 - r) / 4)
    (hWnorm :
      ‖fragPermLocalExponent r (x / Real.sqrt (fragPermSaddleBReal r))‖ ≤ 1) :
    ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleLocalRatio fragPermFun fragPermSaddleAReal fragPermSaddleBReal r
            (x / Real.sqrt (fragPermSaddleBReal r)) -
          saddleThirdPoly fragPermSaddleBReal fragPermSaddleB3Real fragPermSaddleB4Real
            fragPermSaddleB5Real fragPermSaddleB6Real r x)‖
      ≤ fragPermThirdLocalL1Const * (1 - r) ^ (5 / 2 : ℝ) *
          fragPermThirdLocalDom x := by
  let u : ℝ := 1 - r
  let A : ℝ := u ^ (1 / 2 : ℝ)
  let B : ℝ := u
  let D : ℝ := u ^ (3 / 2 : ℝ)
  let E : ℝ := u ^ 2
  let P : ℝ := u ^ (5 / 2 : ℝ)
  let C : ℂ := fragPermThirdScaledCubic r x
  let Q : ℂ := fragPermThirdScaledQuartic r x
  let F : ℂ := fragPermThirdScaledFifth r x
  let S : ℂ := fragPermThirdScaledSixth r x
  let R : ℂ := fragPermThirdScaledRemainder r x
  let W : ℂ := fragPermLocalExponent r (x / Real.sqrt (fragPermSaddleBReal r))
  let y : ℝ := |x|
  let K : ℝ := fragPermThirdScaledRemainderConst
  let T : ℝ := 10 * y ^ 3
  let S1 : ℝ := 10 * y ^ 3 + 10 * y ^ 4 + 40 * y ^ 5 + 10 * y ^ 6 + K * y ^ 7
  let S2 : ℝ := 10 * y ^ 4 + 40 * y ^ 5 + 10 * y ^ 6 + K * y ^ 7
  let S3 : ℝ := 10 * y ^ 6 + K * y ^ 7
  let S4 : ℝ := 40 * y ^ 5 + 10 * y ^ 6 + K * y ^ 7
  let G : ℝ := ∑ k ∈ Finset.range 36, y ^ k
  have hu_pos : 0 < u := by dsimp [u]; linarith [hr.2]
  have hu_nonneg : 0 ≤ u := hu_pos.le
  have hu_le_one : u ≤ 1 := by dsimp [u]; linarith [hr.1]
  have hy0 : 0 ≤ y := by dsimp [y]; exact abs_nonneg x
  have hK_nonneg : 0 ≤ K := by dsimp [K]; exact fragPermThirdScaledRemainderConst_pos.le
  have hA_nonneg : 0 ≤ A := by dsimp [A]; exact Real.rpow_nonneg hu_nonneg _
  have hB_nonneg : 0 ≤ B := by dsimp [B]; exact hu_nonneg
  have hD_nonneg : 0 ≤ D := by dsimp [D]; exact Real.rpow_nonneg hu_nonneg _
  have hE_nonneg : 0 ≤ E := by dsimp [E]; positivity
  have hP_nonneg : 0 ≤ P := by dsimp [P]; exact Real.rpow_nonneg hu_nonneg _
  have hS1_nonneg : 0 ≤ S1 := by dsimp [S1]; positivity
  have hS2_nonneg : 0 ≤ S2 := by dsimp [S2]; positivity
  have hS3_nonneg : 0 ≤ S3 := by dsimp [S3]; positivity
  have hS4_nonneg : 0 ≤ S4 := by dsimp [S4]; positivity
  have hT_nonneg : 0 ≤ T := by dsimp [T]; positivity
  have hrpow_le (a b : ℝ) (hab : a ≤ b) : u ^ b ≤ u ^ a :=
    Real.rpow_le_rpow_of_exponent_ge hu_pos hu_le_one hab
  have hB_le_A : B ≤ A := by
    dsimp [B, A]
    simpa [Real.rpow_one] using (hrpow_le (1 / 2 : ℝ) 1 (by norm_num))
  have hD_le_A : D ≤ A := by
    dsimp [D, A]
    exact hrpow_le (1 / 2 : ℝ) (3 / 2 : ℝ) (by norm_num)
  have hE_le_A : E ≤ A := by
    dsimp [E, A]
    rw [show u ^ 2 = u ^ (2 : ℝ) by exact (Real.rpow_natCast u 2).symm]
    exact hrpow_le (1 / 2 : ℝ) 2 (by norm_num)
  have hP_le_A : P ≤ A := by
    dsimp [P, A]
    exact hrpow_le (1 / 2 : ℝ) (5 / 2 : ℝ) (by norm_num)
  have hD_le_B : D ≤ B := by
    dsimp [D, B]
    simpa [Real.rpow_one] using (hrpow_le 1 (3 / 2 : ℝ) (by norm_num))
  have hE_le_B : E ≤ B := by
    dsimp [E, B]
    simpa [Real.rpow_one, Real.rpow_natCast] using (hrpow_le 1 2 (by norm_num))
  have hP_le_B : P ≤ B := by
    dsimp [P, B]
    simpa [Real.rpow_one] using (hrpow_le 1 (5 / 2 : ℝ) (by norm_num))
  have hE_le_D : E ≤ D := by
    dsimp [E, D]
    rw [show u ^ 2 = u ^ (2 : ℝ) by exact (Real.rpow_natCast u 2).symm]
    exact hrpow_le (3 / 2 : ℝ) 2 (by norm_num)
  have hP_le_D : P ≤ D := by
    dsimp [P, D]
    exact hrpow_le (3 / 2 : ℝ) (5 / 2 : ℝ) (by norm_num)
  have hA2 : A ^ 2 = B := by
    dsimp [A, B]
    calc
      (u ^ (1 / 2 : ℝ)) ^ 2 = u ^ ((1 / 2 : ℝ) * 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hu_nonneg]
        norm_num
      _ = u ^ (1 : ℝ) := by norm_num
      _ = u := by rw [Real.rpow_one]
  have hA3 : A ^ 3 = D := by
    dsimp [A, D]
    calc
      (u ^ (1 / 2 : ℝ)) ^ 3 = u ^ ((1 / 2 : ℝ) * 3) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hu_nonneg]
        norm_num
      _ = u ^ (3 / 2 : ℝ) := by norm_num
  have hA5 : A ^ 5 = P := by
    dsimp [A, P]
    calc
      (u ^ (1 / 2 : ℝ)) ^ 5 = u ^ ((1 / 2 : ℝ) * 5) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hu_nonneg]
        norm_num
      _ = u ^ (5 / 2 : ℝ) := by norm_num
  have hBD : B * D = P := by
    dsimp [B, D, P]
    have h : u ^ (1 : ℝ) * u ^ (3 / 2 : ℝ) = u ^ (5 / 2 : ℝ) := by
      rw [← Real.rpow_add hu_pos]
      norm_num
    simpa [Real.rpow_one] using h
  have hAE : A * E = P := by
    dsimp [A, E, P]
    rw [show u ^ 2 = u ^ (2 : ℝ) by exact (Real.rpow_natCast u 2).symm]
    rw [← Real.rpow_add hu_pos]
    norm_num
  have hA2D : A ^ 2 * D = P := by
    rw [hA2]
    exact hBD
  have hAB2 : A * B ^ 2 = P := by
    have hB2 : B ^ 2 = E := by dsimp [B, E]
    rw [hB2]
    exact hAE
  have hA3B : A ^ 3 * B = P := by
    rw [hA3]
    simpa [mul_comm] using hBD
  have hD2_le_P : D ^ 2 ≤ P := by
    dsimp [D, P]
    calc
      (u ^ (3 / 2 : ℝ)) ^ 2 = u ^ ((3 / 2 : ℝ) * 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hu_nonneg]
        norm_num
      _ = u ^ (3 : ℝ) := by norm_num
      _ ≤ u ^ (5 / 2 : ℝ) := hrpow_le (5 / 2 : ℝ) 3 (by norm_num)
  have hE2_le_P : E ^ 2 ≤ P := by
    dsimp [E, P]
    calc
      (u ^ 2) ^ 2 = u ^ (4 : ℝ) := by
        rw [show u ^ 2 = u ^ (2 : ℝ) by exact (Real.rpow_natCast u 2).symm]
        rw [← Real.rpow_natCast, ← Real.rpow_mul hu_nonneg]
        norm_num
      _ ≤ u ^ (5 / 2 : ℝ) := hrpow_le (5 / 2 : ℝ) 4 (by norm_num)
  have hB3_le_P : B ^ 3 ≤ P := by
    dsimp [B, P]
    rw [show u ^ 3 = u ^ (3 : ℝ) by exact (Real.rpow_natCast u 3).symm]
    exact hrpow_le (5 / 2 : ℝ) 3 (by norm_num)
  have hbpos : 0 < fragPermSaddleBReal r := by
    unfold fragPermSaddleBReal
    have hrpos : 0 < r := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hr.1
    have hnum : 0 < r * (1 + r) := by
      exact mul_pos hrpos (by linarith)
    have hden : 0 < (1 - r) ^ 3 := by
      exact pow_pos (by linarith [hr.2] : 0 < 1 - r) _
    exact div_pos hnum hden
  have hWsplit : W = C + Q + F + S + R := by
    dsimp [W, C, Q, F, S, R]
    exact fragPermThirdLocalExponent_scaled_split r x
  have hPpoly :
      saddleThirdPoly fragPermSaddleBReal fragPermSaddleB3Real fragPermSaddleB4Real
          fragPermSaddleB5Real fragPermSaddleB6Real r x =
        1 + C + Q + C ^ 2 / 2 + F + S + C * Q + C * F + Q ^ 2 / 2 +
          C ^ 3 / 6 + C ^ 2 * Q / 2 + C ^ 4 / 24 := by
    dsimp [C, Q, F, S]
    exact fragPerm_saddleThirdPoly_eq_scaled_terms hbpos
  have herr := complex_exp_third_error_bound C Q F S R W hWsplit
    (by simpa [W] using hWnorm)
  have hC : ‖C‖ ≤ A * T := by
    calc
      ‖C‖ ≤ 10 * A * y ^ 3 := by
        dsimp [C, A, y, u]
        simpa [mul_assoc] using fragPermThirdScaledCubic_norm_le (r := r) (x := x) hr
      _ = A * T := by dsimp [T]; ring
  have hQ_B : ‖Q‖ ≤ 10 * B * y ^ 4 := by
    dsimp [Q, B, y, u]
    simpa [mul_assoc] using fragPermThirdScaledQuartic_norm_le (r := r) (x := x) hr
  have hF_D : ‖F‖ ≤ 40 * D * y ^ 5 := by
    dsimp [F, D, y, u]
    simpa [mul_assoc] using fragPermThirdScaledFifth_norm_le (r := r) (x := x) hr
  have hS_E : ‖S‖ ≤ 10 * E * y ^ 6 := by
    dsimp [S, E, y, u]
    simpa [mul_assoc] using fragPermThirdScaledSixth_norm_le (r := r) (x := x) hr
  have hR_P : ‖R‖ ≤ K * P * y ^ 7 := by
    dsimp [R, K, P, y, u]
    simpa [mul_assoc] using
      fragPermThirdScaledRemainder_norm_le (r := r) (x := x) hr hθδ hδle hδu
  have hQ_A : ‖Q‖ ≤ 10 * A * y ^ 4 := by
    exact hQ_B.trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hB_le_A (by norm_num : (0 : ℝ) ≤ 10))
        (pow_nonneg hy0 4))
  have hF_A : ‖F‖ ≤ 40 * A * y ^ 5 := by
    exact hF_D.trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hD_le_A (by norm_num : (0 : ℝ) ≤ 40))
        (pow_nonneg hy0 5))
  have hS_A : ‖S‖ ≤ 10 * A * y ^ 6 := by
    exact hS_E.trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hE_le_A (by norm_num : (0 : ℝ) ≤ 10))
        (pow_nonneg hy0 6))
  have hR_A : ‖R‖ ≤ K * A * y ^ 7 := by
    exact hR_P.trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hP_le_A hK_nonneg)
        (pow_nonneg hy0 7))
  have hF_B : ‖F‖ ≤ 40 * B * y ^ 5 := by
    exact hF_D.trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hD_le_B (by norm_num : (0 : ℝ) ≤ 40))
        (pow_nonneg hy0 5))
  have hS_B : ‖S‖ ≤ 10 * B * y ^ 6 := by
    exact hS_E.trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hE_le_B (by norm_num : (0 : ℝ) ≤ 10))
        (pow_nonneg hy0 6))
  have hR_B : ‖R‖ ≤ K * B * y ^ 7 := by
    exact hR_P.trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hP_le_B hK_nonneg)
        (pow_nonneg hy0 7))
  have hS_D : ‖S‖ ≤ 10 * D * y ^ 6 := by
    exact hS_E.trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hE_le_D (by norm_num : (0 : ℝ) ≤ 10))
        (pow_nonneg hy0 6))
  have hR_D : ‖R‖ ≤ K * D * y ^ 7 := by
    exact hR_P.trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hP_le_D hK_nonneg)
        (pow_nonneg hy0 7))
  have hWpoly : ‖W‖ ≤ A * S1 := by
    calc
      ‖W‖ = ‖C + Q + F + S + R‖ := by rw [hWsplit]
      _ ≤ ‖C‖ + ‖Q‖ + ‖F‖ + ‖S‖ + ‖R‖ :=
        complex_norm_add5_le C Q F S R
      _ ≤ A * T + 10 * A * y ^ 4 + 40 * A * y ^ 5 +
            10 * A * y ^ 6 + K * A * y ^ 7 := by
          linarith
      _ = A * S1 := by dsimp [S1, T]; ring
  have hU : ‖C + Q + F‖ ≤ A * S1 := by
    have htri : ‖C + Q + F‖ ≤ ‖C‖ + ‖Q‖ + ‖F‖ := by
      calc
        ‖C + Q + F‖ ≤ ‖C + Q‖ + ‖F‖ := norm_add_le _ _
        _ ≤ (‖C‖ + ‖Q‖) + ‖F‖ := by
          have h := norm_add_le C Q
          linarith
        _ = ‖C‖ + ‖Q‖ + ‖F‖ := by ring
    calc
      ‖C + Q + F‖ ≤ ‖C‖ + ‖Q‖ + ‖F‖ := htri
      _ ≤ A * T + 10 * A * y ^ 4 + 40 * A * y ^ 5 := by linarith
      _ ≤ A * S1 := by
        have hextra : 0 ≤ 10 * A * y ^ 6 + K * A * y ^ 7 := by positivity
        dsimp [S1, T]
        nlinarith
  have hY : ‖Q + F + S + R‖ ≤ B * S2 := by
    calc
      ‖Q + F + S + R‖ ≤ ‖Q‖ + ‖F‖ + ‖S‖ + ‖R‖ :=
        complex_norm_add4_le Q F S R
      _ ≤ 10 * B * y ^ 4 + 40 * B * y ^ 5 + 10 * B * y ^ 6 + K * B * y ^ 7 := by
        linarith
      _ = B * S2 := by dsimp [S2]; ring
  have hV : ‖S + R‖ ≤ E * S3 := by
    calc
      ‖S + R‖ ≤ ‖S‖ + ‖R‖ := norm_add_le _ _
      _ ≤ 10 * E * y ^ 6 + K * E * y ^ 7 := by
        have hR_E : ‖R‖ ≤ K * E * y ^ 7 := by
          exact hR_P.trans
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left
                (by
                  dsimp [P, E]
                  rw [show u ^ 2 = u ^ (2 : ℝ) by
                    exact (Real.rpow_natCast u 2).symm]
                  exact hrpow_le 2 (5 / 2 : ℝ) (by norm_num))
                hK_nonneg)
              (pow_nonneg hy0 7))
        linarith
      _ = E * S3 := by dsimp [S3]; ring
  have hZ : ‖F + S + R‖ ≤ D * S4 := by
    have htri : ‖F + S + R‖ ≤ ‖F‖ + ‖S‖ + ‖R‖ := by
      calc
        ‖F + S + R‖ ≤ ‖F + S‖ + ‖R‖ := norm_add_le _ _
        _ ≤ (‖F‖ + ‖S‖) + ‖R‖ := by
          have h := norm_add_le F S
          linarith
        _ = ‖F‖ + ‖S‖ + ‖R‖ := by ring
    calc
      ‖F + S + R‖ ≤ ‖F‖ + ‖S‖ + ‖R‖ := htri
      _ ≤ 40 * D * y ^ 5 + 10 * D * y ^ 6 + K * D * y ^ 7 := by linarith
      _ = D * S4 := by dsimp [S4]; ring
  have hW5 :
      Real.exp 1 * ‖W‖ ^ 5 ≤ Real.exp 1 * P * S1 ^ 5 := by
    calc
      Real.exp 1 * ‖W‖ ^ 5 ≤ Real.exp 1 * (A * S1) ^ 5 :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg W) hWpoly 5) (Real.exp_pos 1).le
      _ = Real.exp 1 * P * S1 ^ 5 := by
        rw [mul_pow, hA5]
        ring
  have hquad :
      ‖W ^ 2 - (C ^ 2 + 2 * C * Q + 2 * C * F + Q ^ 2)‖ ≤
        P * (1600 * y ^ 10 + 800 * y ^ 9 + 2 * S1 * S3 + S3 ^ 2) := by
    have hquad_id :
        W ^ 2 - (C ^ 2 + 2 * C * Q + 2 * C * F + Q ^ 2) =
          F ^ 2 + 2 * Q * F + 2 * (C + Q + F) * (S + R) + (S + R) ^ 2 := by
      rw [hWsplit]
      ring
    have hF2 : ‖F ^ 2‖ ≤ 1600 * P * y ^ 10 := by
      rw [norm_pow]
      calc
        ‖F‖ ^ 2 ≤ (40 * D * y ^ 5) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg F) hF_D 2
        _ = 1600 * D ^ 2 * y ^ 10 := by ring
        _ ≤ 1600 * P * y ^ 10 := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hD2_le_P (by norm_num : (0 : ℝ) ≤ 1600))
            (pow_nonneg hy0 10)
    have hQF : ‖2 * Q * F‖ ≤ 800 * P * y ^ 9 := by
      calc
        ‖2 * Q * F‖ ≤ 2 * ‖Q‖ * ‖F‖ := by
          rw [norm_mul, norm_mul, Complex.norm_ofNat]
        _ ≤ 2 * (10 * B * y ^ 4) * (40 * D * y ^ 5) := by
          gcongr
        _ = 800 * (B * D) * y ^ 9 := by ring
        _ = 800 * P * y ^ 9 := by rw [hBD]
    have hUV : ‖2 * (C + Q + F) * (S + R)‖ ≤ 2 * P * S1 * S3 := by
      calc
        ‖2 * (C + Q + F) * (S + R)‖ ≤
            2 * ‖C + Q + F‖ * ‖S + R‖ := by
          rw [norm_mul, norm_mul, Complex.norm_ofNat]
        _ ≤ 2 * (A * S1) * (E * S3) := by
          gcongr
        _ = 2 * (A * E) * S1 * S3 := by ring
        _ = 2 * P * S1 * S3 := by rw [hAE]
    have hV2 : ‖(S + R) ^ 2‖ ≤ P * S3 ^ 2 := by
      rw [norm_pow]
      calc
        ‖S + R‖ ^ 2 ≤ (E * S3) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg (S + R)) hV 2
        _ = E ^ 2 * S3 ^ 2 := by ring
        _ ≤ P * S3 ^ 2 :=
          mul_le_mul_of_nonneg_right hE2_le_P (pow_nonneg hS3_nonneg 2)
    rw [hquad_id]
    calc
      ‖F ^ 2 + 2 * Q * F + 2 * (C + Q + F) * (S + R) + (S + R) ^ 2‖
          ≤ ‖F ^ 2‖ + ‖2 * Q * F‖ +
              ‖2 * (C + Q + F) * (S + R)‖ + ‖(S + R) ^ 2‖ :=
        complex_norm_add4_le _ _ _ _
      _ ≤ 1600 * P * y ^ 10 + 800 * P * y ^ 9 +
            2 * P * S1 * S3 + P * S3 ^ 2 := by linarith
      _ = P * (1600 * y ^ 10 + 800 * y ^ 9 + 2 * S1 * S3 + S3 ^ 2) := by
        ring
  have hcube :
      ‖W ^ 3 - (C ^ 3 + 3 * C ^ 2 * Q)‖ ≤
        P * (3 * T ^ 2 * S4 + 3 * T * S2 ^ 2 + S2 ^ 3) := by
    have hcube_id :
        W ^ 3 - (C ^ 3 + 3 * C ^ 2 * Q) =
          3 * C ^ 2 * (F + S + R) + 3 * C * (Q + F + S + R) ^ 2 +
            (Q + F + S + R) ^ 3 := by
      rw [hWsplit]
      ring
    have hC2Z : ‖3 * C ^ 2 * (F + S + R)‖ ≤ 3 * P * T ^ 2 * S4 := by
      calc
        ‖3 * C ^ 2 * (F + S + R)‖ ≤ 3 * ‖C‖ ^ 2 * ‖F + S + R‖ := by
          rw [norm_mul, norm_mul, Complex.norm_ofNat, norm_pow]
        _ ≤ 3 * (A * T) ^ 2 * (D * S4) := by
          gcongr
        _ = 3 * (A ^ 2 * D) * T ^ 2 * S4 := by ring
        _ = 3 * P * T ^ 2 * S4 := by rw [hA2D]
    have hCY2 : ‖3 * C * (Q + F + S + R) ^ 2‖ ≤ 3 * P * T * S2 ^ 2 := by
      calc
        ‖3 * C * (Q + F + S + R) ^ 2‖ ≤
            3 * ‖C‖ * ‖Q + F + S + R‖ ^ 2 := by
          rw [norm_mul, norm_mul, Complex.norm_ofNat, norm_pow]
        _ ≤ 3 * (A * T) * (B * S2) ^ 2 := by
          gcongr
        _ = 3 * (A * B ^ 2) * T * S2 ^ 2 := by ring
        _ = 3 * P * T * S2 ^ 2 := by rw [hAB2]
    have hY3 : ‖(Q + F + S + R) ^ 3‖ ≤ P * S2 ^ 3 := by
      rw [norm_pow]
      calc
        ‖Q + F + S + R‖ ^ 3 ≤ (B * S2) ^ 3 :=
          pow_le_pow_left₀ (norm_nonneg (Q + F + S + R)) hY 3
        _ = B ^ 3 * S2 ^ 3 := by ring
        _ ≤ P * S2 ^ 3 :=
          mul_le_mul_of_nonneg_right hB3_le_P (pow_nonneg hS2_nonneg 3)
    rw [hcube_id]
    calc
      ‖3 * C ^ 2 * (F + S + R) + 3 * C * (Q + F + S + R) ^ 2 +
          (Q + F + S + R) ^ 3‖
          ≤ ‖3 * C ^ 2 * (F + S + R)‖ +
              ‖3 * C * (Q + F + S + R) ^ 2‖ +
              ‖(Q + F + S + R) ^ 3‖ := by
            calc
              ‖3 * C ^ 2 * (F + S + R) + 3 * C * (Q + F + S + R) ^ 2 +
                  (Q + F + S + R) ^ 3‖
                  ≤ ‖3 * C ^ 2 * (F + S + R) +
                      3 * C * (Q + F + S + R) ^ 2‖ +
                    ‖(Q + F + S + R) ^ 3‖ := norm_add_le _ _
              _ ≤ (‖3 * C ^ 2 * (F + S + R)‖ +
                    ‖3 * C * (Q + F + S + R) ^ 2‖) +
                    ‖(Q + F + S + R) ^ 3‖ := by
                have h := norm_add_le (3 * C ^ 2 * (F + S + R))
                  (3 * C * (Q + F + S + R) ^ 2)
                linarith
              _ = ‖3 * C ^ 2 * (F + S + R)‖ +
                    ‖3 * C * (Q + F + S + R) ^ 2‖ +
                    ‖(Q + F + S + R) ^ 3‖ := by ring
      _ ≤ 3 * P * T ^ 2 * S4 + 3 * P * T * S2 ^ 2 + P * S2 ^ 3 := by
        linarith
      _ = P * (3 * T ^ 2 * S4 + 3 * T * S2 ^ 2 + S2 ^ 3) := by ring
  have hfour :
      ‖W ^ 4 - C ^ 4‖ ≤
        P * (S2 * (S1 ^ 3 + S1 ^ 2 * T + S1 * T ^ 2 + T ^ 3)) := by
    have hfactor :
        ‖W ^ 3 + W ^ 2 * C + W * C ^ 2 + C ^ 3‖ ≤
          A ^ 3 * (S1 ^ 3 + S1 ^ 2 * T + S1 * T ^ 2 + T ^ 3) := by
      calc
        ‖W ^ 3 + W ^ 2 * C + W * C ^ 2 + C ^ 3‖
            ≤ ‖W ^ 3‖ + ‖W ^ 2 * C‖ + ‖W * C ^ 2‖ + ‖C ^ 3‖ :=
          complex_norm_add4_le _ _ _ _
        _ ≤ (A * S1) ^ 3 + (A * S1) ^ 2 * (A * T) +
              (A * S1) * (A * T) ^ 2 + (A * T) ^ 3 := by
            rw [norm_pow, norm_mul, norm_pow, norm_mul, norm_pow, norm_pow]
            gcongr
        _ = A ^ 3 * (S1 ^ 3 + S1 ^ 2 * T + S1 * T ^ 2 + T ^ 3) := by ring
    have hYdiff : ‖W - C‖ ≤ B * S2 := by
      have hdiff : W - C = Q + F + S + R := by
        rw [hWsplit]
        ring
      rw [hdiff]
      exact hY
    have hfactor_nonneg :
        0 ≤ S1 ^ 3 + S1 ^ 2 * T + S1 * T ^ 2 + T ^ 3 := by positivity
    calc
      ‖W ^ 4 - C ^ 4‖ =
          ‖(W - C) * (W ^ 3 + W ^ 2 * C + W * C ^ 2 + C ^ 3)‖ := by
            congr 1
            ring
      _ ≤ (B * S2) *
          (A ^ 3 * (S1 ^ 3 + S1 ^ 2 * T + S1 * T ^ 2 + T ^ 3)) := by
        rw [norm_mul]
        exact mul_le_mul hYdiff hfactor
          (norm_nonneg _)
          (mul_nonneg hB_nonneg hS2_nonneg)
      _ = (A ^ 3 * B) * (S2 * (S1 ^ 3 + S1 ^ 2 * T + S1 * T ^ 2 + T ^ 3)) := by
        ring
      _ = P * (S2 * (S1 ^ 3 + S1 ^ 2 * T + S1 * T ^ 2 + T ^ 3)) := by
        rw [hA3B]
  have hpoly :
      Real.exp 1 * S1 ^ 5 + K * y ^ 7 +
        (1600 * y ^ 10 + 800 * y ^ 9 + 2 * S1 * S3 + S3 ^ 2) +
        (3 * T ^ 2 * S4 + 3 * T * S2 ^ 2 + S2 ^ 3) +
        S2 * (S1 ^ 3 + S1 ^ 2 * T + S1 * T ^ 2 + T ^ 3)
          ≤ fragPermThirdLocalL1Const * G := by
    simpa [K, S1, S2, S3, S4, G, T] using
      (fragPermThirdLocal_poly_bound (y := y) hy0)
  have hdiff :
      ‖Complex.exp W -
        (1 + C + Q + C ^ 2 / 2 + F + S + C * Q + C * F + Q ^ 2 / 2 +
          C ^ 3 / 6 + C ^ 2 * Q / 2 + C ^ 4 / 24)‖
        ≤ fragPermThirdLocalL1Const * P * G := by
    calc
      ‖Complex.exp W -
        (1 + C + Q + C ^ 2 / 2 + F + S + C * Q + C * F + Q ^ 2 / 2 +
          C ^ 3 / 6 + C ^ 2 * Q / 2 + C ^ 4 / 24)‖
          ≤ Real.exp 1 * ‖W‖ ^ 5 + ‖R‖ +
              ‖W ^ 2 - (C ^ 2 + 2 * C * Q + 2 * C * F + Q ^ 2)‖ +
              ‖W ^ 3 - (C ^ 3 + 3 * C ^ 2 * Q)‖ +
              ‖W ^ 4 - C ^ 4‖ := herr
      _ ≤ Real.exp 1 * P * S1 ^ 5 + K * P * y ^ 7 +
          P * (1600 * y ^ 10 + 800 * y ^ 9 + 2 * S1 * S3 + S3 ^ 2) +
          P * (3 * T ^ 2 * S4 + 3 * T * S2 ^ 2 + S2 ^ 3) +
          P * (S2 * (S1 ^ 3 + S1 ^ 2 * T + S1 * T ^ 2 + T ^ 3)) := by
        linarith
      _ = P * (Real.exp 1 * S1 ^ 5 + K * y ^ 7 +
          (1600 * y ^ 10 + 800 * y ^ 9 + 2 * S1 * S3 + S3 ^ 2) +
          (3 * T ^ 2 * S4 + 3 * T * S2 ^ 2 + S2 ^ 3) +
          S2 * (S1 ^ 3 + S1 ^ 2 * T + S1 * T ^ 2 + T ^ 3)) := by ring
      _ ≤ P * (fragPermThirdLocalL1Const * G) :=
        mul_le_mul_of_nonneg_left hpoly hP_nonneg
      _ = fragPermThirdLocalL1Const * P * G := by ring
  rw [fragPerm_saddleLocalRatio_eq]
  rw [hPpoly]
  change
    ‖Complex.exp (-(x ^ 2) / 2) *
      (Complex.exp W -
        (1 + C + Q + C ^ 2 / 2 + F + S + C * Q + C * F + Q ^ 2 / 2 +
          C ^ 3 / 6 + C ^ 2 * Q / 2 + C ^ 4 / 24))‖
      ≤ fragPermThirdLocalL1Const * P * fragPermThirdLocalDom x
  rw [norm_mul]
  have hgauss :
      ‖Complex.exp (-(x ^ 2) / 2)‖ = Real.exp (-(x ^ 2) / 2) := by
    rw [Complex.norm_exp]
    congr 1
    simp [pow_two]
  rw [hgauss]
  unfold fragPermThirdLocalDom
  dsimp [P, G, y, u]
  calc
    Real.exp (-(x ^ 2) / 2) *
        ‖Complex.exp W -
          (1 + C + Q + C ^ 2 / 2 + F + S + C * Q + C * F + Q ^ 2 / 2 +
            C ^ 3 / 6 + C ^ 2 * Q / 2 + C ^ 4 / 24)‖
        ≤ Real.exp (-(x ^ 2) / 2) *
            (fragPermThirdLocalL1Const * (1 - r) ^ (5 / 2 : ℝ) * G) :=
          mul_le_mul_of_nonneg_left hdiff (Real.exp_pos _).le
    _ = fragPermThirdLocalL1Const * (1 - r) ^ (5 / 2 : ℝ) *
          (Real.exp (-(x ^ 2) / 2) * ∑ k ∈ Finset.range 36, |x| ^ k) := by
      ring

/-- The same fragmented-permutation H-admissible data, but with the narrower
third-order finite-radius window. -/
def fragPermThirdWindowHAdmissible : HAdmissible fragPermFun fragPermSeries where
  ρ := (1 : ℝ≥0∞)
  radFilter := fragPermRadFilter
  a := fragPermSaddleAReal
  b := fragPermSaddleBReal
  δ := fragPermThirdSaddleDeltaReal
  hp := fragPermFun_hasFPowerSeriesAt_zero
  radius_eq := fragPermSeries_radius_eq_one
  radius_pos := by norm_num
  rad_neBot := fragPermRadFilter_neBot
  r_pos := fragPerm_r_pos_eventually
  differentiableOn := fragPerm_differentiableOn_eventually
  f_pos := fragPerm_f_pos_eventually
  b_pos := fragPerm_b_pos_eventually
  δ_pos := fragPerm_third_delta_pos_eventually
  δ_le_pi := fragPerm_third_delta_le_pi_eventually
  δ_sqrt_b_tendsto_atTop := fragPerm_third_delta_sqrt_b_tendsto_atTop
  local_uniform := by
    intro ε hε
    have hlocal := fragPerm_hayman_uniform_estimates.1 ε hε
    filter_upwards [hlocal, fragPerm_third_delta_le_second_delta_eventually] with
      r hloc hδle θ hθ
    exact hloc θ (hθ.trans hδle)
  tail_uniform := by
    rcases fragPerm_tail_third_uniform with ⟨E, hE_nonneg, hdecay, htail⟩
    refine ⟨E, hE_nonneg, ?_, htail⟩
    have hprod := hdecay.mul fragPermThirdCorrScale_tendsto_zero
    have hprod0 :
        Tendsto
          (fun r : ℝ =>
            Real.sqrt (2 * Real.pi * fragPermSaddleBReal r) * E r /
              fragPermThirdCorrScale r * fragPermThirdCorrScale r)
          fragPermRadFilter (𝓝 0) := by
      simpa using hprod
    refine Tendsto.congr' ?_ hprod0
    filter_upwards [fragPermThirdCorrScale_pos_eventually] with r hpos
    field_simp [hpos.ne']

def fragPermThirdWindowSaddleSequence :
    SaddleSequence fragPermThirdWindowHAdmissible where
  r := fragPermSaddleRadius
  tendsTo := by
    simpa [fragPermThirdWindowHAdmissible] using fragPermSaddleRadius_tendsto_radFilter
  saddle_eq := by
    exact Eventually.of_forall fun n => by
      change fragPermSaddleAReal (fragPermSaddleRadius n) = (n : ℝ)
      exact fragPermSaddleAReal_radius n

private lemma fragPerm_third_local_integrand_continuous (r : ℝ)
    (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1) :
    Continuous fun x : ℝ =>
      ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleLocalRatio fragPermFun fragPermSaddleAReal fragPermSaddleBReal r
            (x / Real.sqrt (fragPermSaddleBReal r)) -
          saddleThirdPoly fragPermSaddleBReal fragPermSaddleB3Real fragPermSaddleB4Real
            fragPermSaddleB5Real fragPermSaddleB6Real r x)‖ := by
  have hr0 : 0 ≤ r := (lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hr.1).le
  have hden_circle :
      ∀ x : ℝ,
        1 - (r : ℂ) * Complex.exp (((x / Real.sqrt (fragPermSaddleBReal r) : ℝ) : ℂ) * Complex.I) ≠ 0 := by
    intro x hzero
    have hz :
        (r : ℂ) * Complex.exp (((x / Real.sqrt (fragPermSaddleBReal r) : ℝ) : ℂ) * Complex.I) = 1 := by
      exact (sub_eq_zero.mp hzero).symm
    have hexp_norm :
        ‖Complex.exp (((x / Real.sqrt (fragPermSaddleBReal r) : ℝ) : ℂ) * Complex.I)‖ = 1 := by
      rw [Complex.norm_exp]
      simp
    have hnorm_left :
        ‖(r : ℂ) * Complex.exp (((x / Real.sqrt (fragPermSaddleBReal r) : ℝ) : ℂ) * Complex.I)‖ = r := by
      have hr_norm : ‖(r : ℂ)‖ = r :=
        (RCLike.norm_ofReal (K := ℂ) r).trans (abs_of_nonneg hr0)
      rw [norm_mul, hr_norm, hexp_norm, mul_one]
    have hnorm_one :
        ‖(r : ℂ) * Complex.exp (((x / Real.sqrt (fragPermSaddleBReal r) : ℝ) : ℂ) * Complex.I)‖ = 1 := by
      rw [hz]
      norm_num
    linarith [hr.2]
  have hden_real : (1 : ℂ) - (r : ℂ) ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    norm_num at hre
    linarith [hr.2]
  have h :
      Continuous fun x : ℝ =>
        ‖Complex.exp (-(x ^ 2) / 2) *
          (Complex.exp (fragPermLocalExponent r (x / Real.sqrt (fragPermSaddleBReal r))) -
            saddleThirdPoly fragPermSaddleBReal fragPermSaddleB3Real fragPermSaddleB4Real
              fragPermSaddleB5Real fragPermSaddleB6Real r x)‖ := by
    have hzcont :
        Continuous fun x : ℝ =>
          (r : ℂ) * Complex.exp (((x / Real.sqrt (fragPermSaddleBReal r) : ℝ) : ℂ) * Complex.I) := by
      fun_prop
    have hfragCircle :
        Continuous fun x : ℝ =>
          fragPermH ((r : ℂ) *
            Complex.exp (((x / Real.sqrt (fragPermSaddleBReal r) : ℝ) : ℂ) * Complex.I)) := by
      unfold fragPermH
      exact hzcont.div (continuous_const.sub hzcont) hden_circle
    have hlin :
        Continuous fun x : ℝ =>
          ((fragPermSaddleAReal r * (x / Real.sqrt (fragPermSaddleBReal r)) : ℝ) : ℂ) *
            Complex.I := by
      fun_prop
    have hquad :
        Continuous fun x : ℝ =>
          ((fragPermSaddleBReal r * (x / Real.sqrt (fragPermSaddleBReal r)) ^ 2 / 2 : ℝ) : ℂ) := by
      fun_prop
    have hlocal :
        Continuous fun x : ℝ =>
          fragPermLocalExponent r (x / Real.sqrt (fragPermSaddleBReal r)) := by
      unfold fragPermLocalExponent
      exact ((hfragCircle.sub continuous_const).sub hlin).add hquad
    have hsaddle :
        Continuous fun x : ℝ =>
          saddleThirdPoly fragPermSaddleBReal fragPermSaddleB3Real fragPermSaddleB4Real
            fragPermSaddleB5Real fragPermSaddleB6Real r x := by
      unfold saddleThirdPoly saddleSecondPoly
      fun_prop
    have hgauss : Continuous fun x : ℝ => Complex.exp (-(x ^ 2) / 2) := by
      fun_prop
    exact (hgauss.mul ((Complex.continuous_exp.comp hlocal).sub hsaddle)).norm
  simpa [fragPerm_saddleLocalRatio_eq] using h

private lemma fragPerm_second_local_integrand_continuous (r : ℝ)
    (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1) :
    Continuous fun x : ℝ =>
      ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleLocalRatio fragPermFun fragPermSaddleAReal fragPermSaddleBReal r
            (x / Real.sqrt (fragPermSaddleBReal r)) -
          saddleSecondPoly fragPermSaddleBReal fragPermSaddleB3Real fragPermSaddleB4Real r x)‖ := by
  have hr0 : 0 ≤ r := (lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hr.1).le
  have hden_circle :
      ∀ x : ℝ,
        1 - (r : ℂ) * Complex.exp (((x / Real.sqrt (fragPermSaddleBReal r) : ℝ) : ℂ) * Complex.I) ≠ 0 := by
    intro x hzero
    have hz :
        (r : ℂ) * Complex.exp (((x / Real.sqrt (fragPermSaddleBReal r) : ℝ) : ℂ) * Complex.I) = 1 := by
      exact (sub_eq_zero.mp hzero).symm
    have hexp_norm :
        ‖Complex.exp (((x / Real.sqrt (fragPermSaddleBReal r) : ℝ) : ℂ) * Complex.I)‖ = 1 := by
      rw [Complex.norm_exp]
      simp
    have hnorm_left :
        ‖(r : ℂ) * Complex.exp (((x / Real.sqrt (fragPermSaddleBReal r) : ℝ) : ℂ) * Complex.I)‖ = r := by
      have hr_norm : ‖(r : ℂ)‖ = r :=
        (RCLike.norm_ofReal (K := ℂ) r).trans (abs_of_nonneg hr0)
      rw [norm_mul, hr_norm, hexp_norm, mul_one]
    have hnorm_one :
        ‖(r : ℂ) * Complex.exp (((x / Real.sqrt (fragPermSaddleBReal r) : ℝ) : ℂ) * Complex.I)‖ = 1 := by
      rw [hz]
      norm_num
    linarith [hr.2]
  have hden_real : (1 : ℂ) - (r : ℂ) ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    norm_num at hre
    linarith [hr.2]
  have h :
      Continuous fun x : ℝ =>
        ‖Complex.exp (-(x ^ 2) / 2) *
          (Complex.exp (fragPermLocalExponent r (x / Real.sqrt (fragPermSaddleBReal r))) -
            saddleSecondPoly fragPermSaddleBReal fragPermSaddleB3Real fragPermSaddleB4Real r x)‖ := by
    have hzcont :
        Continuous fun x : ℝ =>
          (r : ℂ) * Complex.exp (((x / Real.sqrt (fragPermSaddleBReal r) : ℝ) : ℂ) * Complex.I) := by
      fun_prop
    have hfragCircle :
        Continuous fun x : ℝ =>
          fragPermH ((r : ℂ) *
            Complex.exp (((x / Real.sqrt (fragPermSaddleBReal r) : ℝ) : ℂ) * Complex.I)) := by
      unfold fragPermH
      exact hzcont.div (continuous_const.sub hzcont) hden_circle
    have hlin :
        Continuous fun x : ℝ =>
          ((fragPermSaddleAReal r * (x / Real.sqrt (fragPermSaddleBReal r)) : ℝ) : ℂ) *
            Complex.I := by
      fun_prop
    have hquad :
        Continuous fun x : ℝ =>
          ((fragPermSaddleBReal r * (x / Real.sqrt (fragPermSaddleBReal r)) ^ 2 / 2 : ℝ) : ℂ) := by
      fun_prop
    have hlocal :
        Continuous fun x : ℝ =>
          fragPermLocalExponent r (x / Real.sqrt (fragPermSaddleBReal r)) := by
      unfold fragPermLocalExponent
      exact ((hfragCircle.sub continuous_const).sub hlin).add hquad
    have hsaddle :
        Continuous fun x : ℝ =>
          saddleSecondPoly fragPermSaddleBReal fragPermSaddleB3Real fragPermSaddleB4Real r x := by
      unfold saddleSecondPoly
      fun_prop
    have hgauss : Continuous fun x : ℝ => Complex.exp (-(x ^ 2) / 2) := by
      fun_prop
    exact (hgauss.mul ((Complex.continuous_exp.comp hlocal).sub hsaddle)).norm
  simpa [fragPerm_saddleLocalRatio_eq] using h

private lemma fragPermThirdCorrScale_div_secondCorrScale_tendsto_zero :
    Tendsto
      (fun r : ℝ => fragPermThirdCorrScale r / fragPermSecondCorrScale r)
      fragPermRadFilter (𝓝 0) := by
  have hone :
      Tendsto (fun r : ℝ => 1 - r) fragPermRadFilter (𝓝 (0 : ℝ)) :=
    fragPerm_one_sub_tendsto_nhdsGT_zero.mono_right
      (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Set.Ioi (0 : ℝ)))
  refine Tendsto.congr' ?_ hone
  filter_upwards [fragPerm_eventually_Ioo_zero_one] with r hr
  unfold fragPermThirdCorrScale fragPermSecondCorrScale
  have hu : 1 - r ≠ 0 := by linarith [hr.2]
  field_simp [hu]

lemma fragPerm_thirdWindow_local_second_L1 :
    Tendsto
      (fun r : ℝ =>
        (∫ x in -(fragPermThirdSaddleDeltaReal r * Real.sqrt (fragPermSaddleBReal r))..
          (fragPermThirdSaddleDeltaReal r * Real.sqrt (fragPermSaddleBReal r)),
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleLocalRatio fragPermFun fragPermSaddleAReal fragPermSaddleBReal r
                (x / Real.sqrt (fragPermSaddleBReal r)) -
              saddleSecondPoly fragPermSaddleBReal fragPermSaddleB3Real
                fragPermSaddleB4Real r x)‖) /
            fragPermSecondCorrScale r)
        fragPermRadFilter (𝓝 0) := by
  have hwide := fragPerm_local_second_L1
  refine squeeze_zero' ?_ ?_ hwide
  · filter_upwards [fragPerm_eventually_Ioo_zero_one, fragPermSecondCorrScale_pos_eventually] with
      r hr hcorr
    let L : ℝ := fragPermThirdSaddleDeltaReal r * Real.sqrt (fragPermSaddleBReal r)
    have hLnonneg : 0 ≤ L := by
      dsimp [L, fragPermThirdSaddleDeltaReal]
      positivity
    have hle : -L ≤ L := by linarith
    have hint_nonneg :
        0 ≤ ∫ x in -L..L,
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleLocalRatio fragPermFun fragPermSaddleAReal fragPermSaddleBReal r
                (x / Real.sqrt (fragPermSaddleBReal r)) -
              saddleSecondPoly fragPermSaddleBReal fragPermSaddleB3Real fragPermSaddleB4Real r x)‖ :=
      intervalIntegral.integral_nonneg hle (fun _ _ => norm_nonneg _)
    exact div_nonneg hint_nonneg hcorr.le
  · filter_upwards [fragPerm_eventually_Ioo_half_one,
      fragPerm_third_delta_le_second_delta_eventually,
      fragPermSecondCorrScale_pos_eventually] with r hr hδle hcorr
    let L3 : ℝ := fragPermThirdSaddleDeltaReal r * Real.sqrt (fragPermSaddleBReal r)
    let L2 : ℝ := fragPermSaddleDeltaReal r * Real.sqrt (fragPermSaddleBReal r)
    let F : ℝ → ℝ := fun x =>
      ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleLocalRatio fragPermFun fragPermSaddleAReal fragPermSaddleBReal r
            (x / Real.sqrt (fragPermSaddleBReal r)) -
          saddleSecondPoly fragPermSaddleBReal fragPermSaddleB3Real fragPermSaddleB4Real r x)‖
    have hsqrt_nonneg : 0 ≤ Real.sqrt (fragPermSaddleBReal r) := Real.sqrt_nonneg _
    have hL3nonneg : 0 ≤ L3 := by
      dsimp [L3, fragPermThirdSaddleDeltaReal]
      positivity
    have hL2nonneg : 0 ≤ L2 := by
      dsimp [L2, fragPermSaddleDeltaReal]
      positivity
    have hLle : L3 ≤ L2 := by
      dsimp [L3, L2]
      exact mul_le_mul_of_nonneg_right hδle hsqrt_nonneg
    have hsmall_le_big_left : -L2 ≤ -L3 := by linarith
    have hsmall_le_big_right : L3 ≤ L2 := hLle
    have hsmall_order : -L3 ≤ L3 := by linarith
    have hFnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc (-L2) L2)] F :=
      Eventually.of_forall fun x => norm_nonneg _
    have hFint : IntervalIntegrable F volume (-L2) L2 := by
      exact (fragPerm_second_local_integrand_continuous r hr).intervalIntegrable _ _
    have hInt :
        (∫ x in -L3..L3, F x) ≤ ∫ x in -L2..L2, F x :=
      intervalIntegral.integral_mono_interval hsmall_le_big_left hsmall_order
        hsmall_le_big_right hFnonneg hFint
    have hdiv :
        (∫ x in -L3..L3, F x) / fragPermSecondCorrScale r ≤
          (∫ x in -L2..L2, F x) / fragPermSecondCorrScale r :=
      div_le_div_of_nonneg_right hInt hcorr.le
    simpa [L3, L2, F] using hdiv

def fragPermThirdWindowSecondOrder :
    SecondOrderHAdmissible fragPermThirdWindowHAdmissible where
  b3 := fragPermSaddleB3Real
  b4 := fragPermSaddleB4Real
  corrScale := fragPermSecondCorrScale
  corrScale_pos := by
    simpa [fragPermThirdWindowHAdmissible] using fragPermSecondCorrScale_pos_eventually
  corrScale_tendsto_zero := by
    simpa [fragPermThirdWindowHAdmissible] using fragPermSecondCorrScale_tendsto_zero
  corrScale_dominates_correction := by
    refine ⟨200, by norm_num, ?_⟩
    simpa [fragPermThirdWindowHAdmissible] using
      fragPerm_saddleCorrectionScale_le_oneSub_eventually
  local_second_L1 := by
    simpa [fragPermThirdWindowHAdmissible] using fragPerm_thirdWindow_local_second_L1
  tail_second_uniform := by
    rcases fragPerm_tail_third_uniform with ⟨E, hE_nonneg, hdecay, htail⟩
    refine ⟨E, ?_, ?_, ?_⟩
    · simpa [fragPermThirdWindowHAdmissible] using hE_nonneg
    · have hprod := hdecay.mul fragPermThirdCorrScale_div_secondCorrScale_tendsto_zero
      have hprod0 :
          Tendsto
            (fun r : ℝ =>
              Real.sqrt (2 * Real.pi * fragPermSaddleBReal r) * E r /
                fragPermThirdCorrScale r *
                  (fragPermThirdCorrScale r / fragPermSecondCorrScale r))
            fragPermRadFilter (𝓝 0) := by
        simpa using hprod
      refine Tendsto.congr' ?_ hprod0
      filter_upwards [fragPermThirdCorrScale_pos_eventually,
        fragPermSecondCorrScale_pos_eventually] with r hthird hsecond
      field_simp [hthird.ne', hsecond.ne']
      simp [fragPermThirdWindowHAdmissible, mul_comm, mul_left_comm, mul_assoc]
    · simpa [fragPermThirdWindowHAdmissible] using htail

theorem fragPerm_thirdWindow_local_third_L1 :
    Tendsto
      (fun r : ℝ =>
        (∫ x in -(fragPermThirdSaddleDeltaReal r * Real.sqrt (fragPermSaddleBReal r))..
          (fragPermThirdSaddleDeltaReal r * Real.sqrt (fragPermSaddleBReal r)),
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleLocalRatio fragPermFun fragPermSaddleAReal fragPermSaddleBReal r
                (x / Real.sqrt (fragPermSaddleBReal r)) -
              saddleThirdPoly fragPermSaddleBReal fragPermSaddleB3Real
                fragPermSaddleB4Real fragPermSaddleB5Real fragPermSaddleB6Real r x)‖) /
            fragPermThirdCorrScale r)
        fragPermRadFilter (𝓝 0) := by
  let M : ℝ := ∫ x : ℝ, fragPermThirdLocalDom x
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact fragPermThirdLocalDom_integral_nonneg
  have hpow_tendsto :
      Tendsto (fun r : ℝ => (1 - r) ^ (1 / 2 : ℝ))
        fragPermRadFilter (𝓝 0) := by
    have hu :
        Tendsto (fun r : ℝ => 1 - r) fragPermRadFilter (𝓝 (0 : ℝ)) :=
      fragPerm_one_sub_tendsto_nhdsGT_zero.mono_right
        (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Set.Ioi (0 : ℝ)))
    simpa [Function.comp_def] using
      ((Real.continuousAt_rpow_const (0 : ℝ) (1 / 2 : ℝ)
        (Or.inr (by norm_num : (0 : ℝ) ≤ 1 / 2))).tendsto.comp hu)
  have hupper_tendsto :
      Tendsto
        (fun r : ℝ => fragPermThirdLocalL1Const * M * (1 - r) ^ (1 / 2 : ℝ))
        fragPermRadFilter (𝓝 0) := by
    simpa [mul_assoc] using hpow_tendsto.const_mul (fragPermThirdLocalL1Const * M)
  refine squeeze_zero' ?_ ?_ hupper_tendsto
  · filter_upwards [fragPerm_eventually_Ioo_zero_one, fragPermThirdCorrScale_pos_eventually] with
      r hr hcorr
    let L : ℝ := fragPermThirdSaddleDeltaReal r * Real.sqrt (fragPermSaddleBReal r)
    have hLnonneg : 0 ≤ L := by
      dsimp [L]
      exact mul_nonneg
        (by
          unfold fragPermThirdSaddleDeltaReal
          exact Real.rpow_nonneg (by linarith [hr.2] : 0 ≤ 1 - r) _)
        (Real.sqrt_nonneg _)
    have hle : -L ≤ L := by linarith
    have hint_nonneg :
        0 ≤ ∫ x in -L..L,
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleLocalRatio fragPermFun fragPermSaddleAReal fragPermSaddleBReal r
                (x / Real.sqrt (fragPermSaddleBReal r)) -
              saddleThirdPoly fragPermSaddleBReal fragPermSaddleB3Real
                fragPermSaddleB4Real fragPermSaddleB5Real fragPermSaddleB6Real r x)‖ :=
      intervalIntegral.integral_nonneg hle (fun _ _ => norm_nonneg _)
    exact div_nonneg hint_nonneg hcorr.le
  · filter_upwards [fragPerm_eventually_Ioo_half_one,
      fragPerm_third_delta_le_one_eventually,
      fragPerm_third_delta_le_one_sub_quarter_eventually,
      fragPerm_third_delta_le_second_delta_eventually,
      fragPerm_delta_le_one_eventually,
      fragPerm_delta_le_one_sub_quarter_eventually,
      fragPermLocalBound_tendsto_zero.eventually_le_const zero_lt_one,
      fragPermThirdCorrScale_pos_eventually] with
      r hr hδ3le hδ3u hδ32 hδ2le hδ2u hlocSmall hcorrPos
    let L : ℝ := fragPermThirdSaddleDeltaReal r * Real.sqrt (fragPermSaddleBReal r)
    let F : ℝ → ℝ := fun x =>
      ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleLocalRatio fragPermFun fragPermSaddleAReal fragPermSaddleBReal r
            (x / Real.sqrt (fragPermSaddleBReal r)) -
          saddleThirdPoly fragPermSaddleBReal fragPermSaddleB3Real fragPermSaddleB4Real
            fragPermSaddleB5Real fragPermSaddleB6Real r x)‖
    let H : ℝ → ℝ := fun x =>
      (fragPermThirdLocalL1Const * (1 - r) ^ (5 / 2 : ℝ)) * fragPermThirdLocalDom x
    have hbpos : 0 < fragPermSaddleBReal r := by
      unfold fragPermSaddleBReal
      have hrpos : 0 < r := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hr.1
      have hnum : 0 < r * (1 + r) := mul_pos hrpos (by linarith)
      have hden : 0 < (1 - r) ^ 3 := pow_pos (by linarith [hr.2] : 0 < 1 - r) _
      exact div_pos hnum hden
    have hsqrt_pos : 0 < Real.sqrt (fragPermSaddleBReal r) := Real.sqrt_pos.mpr hbpos
    have hLnonneg : 0 ≤ L := by
      dsimp [L]
      exact mul_nonneg
        (by
          unfold fragPermThirdSaddleDeltaReal
          exact Real.rpow_nonneg (by linarith [hr.2] : 0 ≤ 1 - r) _)
        (Real.sqrt_nonneg _)
    have hle : -L ≤ L := by linarith
    have hpoint : ∀ x ∈ Set.Icc (-L) L, F x ≤ H x := by
      intro x hx
      have hxabs : |x| ≤ L := by
        exact abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
      have hθδ3 : |x / Real.sqrt (fragPermSaddleBReal r)| ≤ fragPermThirdSaddleDeltaReal r := by
        rw [abs_div, abs_of_pos hsqrt_pos]
        calc
          |x| / Real.sqrt (fragPermSaddleBReal r) ≤
              L / Real.sqrt (fragPermSaddleBReal r) :=
            div_le_div_of_nonneg_right hxabs hsqrt_pos.le
          _ = fragPermThirdSaddleDeltaReal r := by
            dsimp [L]
            exact mul_div_cancel_right₀ (fragPermThirdSaddleDeltaReal r) hsqrt_pos.ne'
      have hθδ2 : |x / Real.sqrt (fragPermSaddleBReal r)| ≤ fragPermSaddleDeltaReal r :=
        hθδ3.trans hδ32
      have hWnorm :
          ‖fragPermLocalExponent r (x / Real.sqrt (fragPermSaddleBReal r))‖ ≤ 1 :=
        (fragPerm_local_exponent_norm_le
          (lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hr.1).le hr.2
          hδ2le hδ2u hθδ2).trans hlocSmall
      have hb := fragPerm_third_local_integrand_bound hr hθδ3 hδ3le hδ3u hWnorm
      dsimp [F, H]
      exact hb
    have hFint : IntervalIntegrable F volume (-L) L := by
      exact (fragPerm_third_local_integrand_continuous r hr).intervalIntegrable _ _
    have hHint : IntervalIntegrable H volume (-L) L := by
      exact (fragPermThirdLocalDom_continuous.const_mul
        (fragPermThirdLocalL1Const * (1 - r) ^ (5 / 2 : ℝ))).intervalIntegrable _ _
    have hIntBound :
        (∫ x in -L..L, F x) ≤
          (fragPermThirdLocalL1Const * (1 - r) ^ (5 / 2 : ℝ)) * M := by
      have hconst_nonneg :
          0 ≤ fragPermThirdLocalL1Const * (1 - r) ^ (5 / 2 : ℝ) := by
        exact mul_nonneg fragPermThirdLocalL1Const_pos.le
          (Real.rpow_nonneg (by linarith [hr.2] : 0 ≤ 1 - r) _)
      calc
        (∫ x in -L..L, F x) ≤ ∫ x in -L..L, H x :=
          intervalIntegral.integral_mono_on hle hFint hHint hpoint
        _ = (fragPermThirdLocalL1Const * (1 - r) ^ (5 / 2 : ℝ)) *
              (∫ x in -L..L, fragPermThirdLocalDom x) := by
          dsimp [H]
          rw [intervalIntegral.integral_const_mul]
        _ ≤ (fragPermThirdLocalL1Const * (1 - r) ^ (5 / 2 : ℝ)) * M := by
          exact mul_le_mul_of_nonneg_left
            (by dsimp [M]; exact fragPermThirdLocalDom_window_le_integral hLnonneg)
            hconst_nonneg
    have hmain :
        (∫ x in -L..L, F x) / fragPermThirdCorrScale r ≤
          ((fragPermThirdLocalL1Const * (1 - r) ^ (5 / 2 : ℝ)) * M) /
            fragPermThirdCorrScale r := by
      exact div_le_div_of_nonneg_right hIntBound hcorrPos.le
    have hu_pos : 0 < 1 - r := by linarith [hr.2]
    have hu_nonneg : 0 ≤ 1 - r := hu_pos.le
    have hratio :
        (1 - r) ^ (5 / 2 : ℝ) / (1 - r) ^ 2 =
          (1 - r) ^ (1 / 2 : ℝ) := by
      rw [show (1 - r) ^ 2 = (1 - r) ^ (2 : ℝ) by
        exact (Real.rpow_natCast (1 - r) 2).symm]
      rw [div_eq_mul_inv, ← Real.rpow_neg hu_nonneg (2 : ℝ),
        ← Real.rpow_add hu_pos]
      norm_num
    calc
      ((∫ x in -(fragPermThirdSaddleDeltaReal r * Real.sqrt (fragPermSaddleBReal r))..
          (fragPermThirdSaddleDeltaReal r * Real.sqrt (fragPermSaddleBReal r)),
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleLocalRatio fragPermFun fragPermSaddleAReal fragPermSaddleBReal r
                (x / Real.sqrt (fragPermSaddleBReal r)) -
              saddleThirdPoly fragPermSaddleBReal fragPermSaddleB3Real
                fragPermSaddleB4Real fragPermSaddleB5Real fragPermSaddleB6Real r x)‖) /
          fragPermThirdCorrScale r)
          = (∫ x in -L..L, F x) / fragPermThirdCorrScale r := by rfl
      _ ≤ ((fragPermThirdLocalL1Const * (1 - r) ^ (5 / 2 : ℝ)) * M) /
            fragPermThirdCorrScale r := hmain
      _ = fragPermThirdLocalL1Const * M * (1 - r) ^ (1 / 2 : ℝ) := by
        unfold fragPermThirdCorrScale
        calc
          ((fragPermThirdLocalL1Const * (1 - r) ^ (5 / 2 : ℝ)) * M) /
              (1 - r) ^ 2
              = fragPermThirdLocalL1Const * M *
                  ((1 - r) ^ (5 / 2 : ℝ) / (1 - r) ^ 2) := by
                field_simp [(pow_pos hu_pos 2).ne']
          _ = fragPermThirdLocalL1Const * M * (1 - r) ^ (1 / 2 : ℝ) := by
            rw [hratio]

theorem fragPerm_thirdWindow_local_third_L1_robust :
    Tendsto
      (fun r : ℝ =>
        (∫ x in -(fragPermThirdSaddleDeltaReal r * Real.sqrt (fragPermSaddleBReal r))..
          (fragPermThirdSaddleDeltaReal r * Real.sqrt (fragPermSaddleBReal r)),
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleLocalRatio fragPermFun fragPermSaddleAReal fragPermSaddleBReal r
                (x / Real.sqrt (fragPermSaddleBReal r)) -
              saddleThirdPoly fragPermSaddleBReal fragPermSaddleB3Real
                fragPermSaddleB4Real fragPermSaddleB5Real fragPermSaddleB6Real r x)‖) /
            fragPermThirdRobustCorrScale r)
        fragPermRadFilter (𝓝 0) := by
  have htrue := fragPerm_thirdWindow_local_third_L1
  have hratio := fragPermThirdCorrScale_div_secondCorrScale_tendsto_zero
  have hprod := htrue.mul hratio
  have hprod0 :
      Tendsto
        (fun r : ℝ =>
          ((∫ x in -(fragPermThirdSaddleDeltaReal r * Real.sqrt (fragPermSaddleBReal r))..
            (fragPermThirdSaddleDeltaReal r * Real.sqrt (fragPermSaddleBReal r)),
            ‖Complex.exp (-(x ^ 2) / 2) *
              (saddleLocalRatio fragPermFun fragPermSaddleAReal fragPermSaddleBReal r
                  (x / Real.sqrt (fragPermSaddleBReal r)) -
                saddleThirdPoly fragPermSaddleBReal fragPermSaddleB3Real
                  fragPermSaddleB4Real fragPermSaddleB5Real fragPermSaddleB6Real r x)‖) /
              fragPermThirdCorrScale r) *
            (fragPermThirdCorrScale r / fragPermSecondCorrScale r))
        fragPermRadFilter (𝓝 0) := by
    simpa using hprod
  refine Tendsto.congr' ?_ hprod0
  filter_upwards [fragPermThirdCorrScale_pos_eventually,
    fragPermSecondCorrScale_pos_eventually] with r hthird hsecond
  field_simp [fragPermThirdRobustCorrScale, hthird.ne', hsecond.ne']
  simp [fragPermThirdRobustCorrScale, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

def fragPermThirdWindowThirdOrder :
    ThirdOrderHAdmissible fragPermThirdWindowHAdmissible fragPermThirdWindowSecondOrder where
  b5 := fragPermSaddleB5Real
  b6 := fragPermSaddleB6Real
  corrScale3 := fragPermThirdRobustCorrScale
  corrScale3_pos := by
    simpa [fragPermThirdWindowHAdmissible, fragPermThirdRobustCorrScale] using
      fragPermSecondCorrScale_pos_eventually
  corrScale3_tendsto_zero := by
    simpa [fragPermThirdWindowHAdmissible, fragPermThirdRobustCorrScale] using
      fragPermSecondCorrScale_tendsto_zero
  corrScale3_dominates_correction := by
    rcases fragPerm_saddleThirdCorrectionScale_le_sq_eventually with
      ⟨K3, hK3nonneg, hK3⟩
    refine ⟨200 + K3, by positivity, ?_⟩
    filter_upwards [fragPerm_saddleCorrectionScale_le_oneSub_eventually, hK3,
      fragPerm_eventually_Ioo_zero_one] with r hsecond hpure hr
    have hthird_le_second : fragPermThirdCorrScale r ≤ fragPermSecondCorrScale r := by
      unfold fragPermThirdCorrScale fragPermSecondCorrScale
      have hu_nonneg : 0 ≤ 1 - r := by linarith [hr.2]
      have hu_le_one : 1 - r ≤ 1 := by linarith [hr.1]
      nlinarith [sq_nonneg (1 - r)]
    have hpure_second :
        |fragPermSaddleB6Real r| / (fragPermSaddleBReal r) ^ 3
          + |fragPermSaddleB3Real r * fragPermSaddleB5Real r| /
              (fragPermSaddleBReal r) ^ 4
          + (fragPermSaddleB4Real r) ^ 2 / (fragPermSaddleBReal r) ^ 4
          + (fragPermSaddleB3Real r) ^ 2 * |fragPermSaddleB4Real r| /
              (fragPermSaddleBReal r) ^ 5
          + (fragPermSaddleB3Real r) ^ 4 / (fragPermSaddleBReal r) ^ 6
            ≤ K3 * fragPermSecondCorrScale r :=
      hpure.trans (mul_le_mul_of_nonneg_left hthird_le_second hK3nonneg)
    have hsecond_exp := hsecond
    simp only [saddleCorrectionScale, fragPermSaddleBReal] at hsecond_exp
    have hpure_second_exp := hpure_second
    simp only [fragPermSaddleBReal] at hpure_second_exp
    rw [saddleThirdCorrectionScale_apply]
    dsimp [fragPermThirdWindowHAdmissible, fragPermThirdWindowSecondOrder,
      fragPermThirdRobustCorrScale]
    nlinarith [hsecond_exp, hpure_second_exp]
  local_third_L1 := by
    simpa [fragPermThirdWindowHAdmissible, fragPermThirdWindowSecondOrder,
      fragPermThirdRobustCorrScale] using
      fragPerm_thirdWindow_local_third_L1_robust
  tail_third_uniform := by
    rcases fragPerm_tail_third_uniform with ⟨E, hE_nonneg, hdecay, htail⟩
    refine ⟨E, ?_, ?_, ?_⟩
    · simpa [fragPermThirdWindowHAdmissible] using hE_nonneg
    · have hprod := hdecay.mul fragPermThirdCorrScale_div_secondCorrScale_tendsto_zero
      have hprod0 :
          Tendsto
            (fun r : ℝ =>
              Real.sqrt (2 * Real.pi * fragPermSaddleBReal r) * E r /
                fragPermThirdCorrScale r *
                  (fragPermThirdCorrScale r / fragPermSecondCorrScale r))
            fragPermRadFilter (𝓝 0) := by
        simpa using hprod
      refine Tendsto.congr' ?_ hprod0
      filter_upwards [fragPermThirdCorrScale_pos_eventually,
        fragPermSecondCorrScale_pos_eventually] with r hthird hsecond
      field_simp [fragPermThirdWindowHAdmissible, fragPermThirdRobustCorrScale,
        hthird.ne', hsecond.ne']
      simp [fragPermThirdWindowHAdmissible, fragPermThirdRobustCorrScale,
        mul_comm, mul_left_comm, mul_assoc]
    · simpa [fragPermThirdWindowHAdmissible] using htail

theorem fragPerm_coeff_thirdOrder_saddle_from_HAdmissible :
    (fun n : ℕ =>
      fragPermThirdOrderSeriesError n)
      =o[atTop]
    (fun n : ℕ => (fragPermThirdRobustCorrScale (fragPermSaddleRadius n) : ℂ)) := by
  have h :=
    coeff_thirdOrder_saddle
      fragPermThirdWindowHAdmissible fragPermThirdWindowSecondOrder
      fragPermThirdWindowThirdOrder fragPermThirdWindowSaddleSequence
  simpa [fragPermThirdOrderSeriesError, fragPermThirdOrderSaddleScale,
    fragPermSecondCorrectionAtSaddle, fragPermThirdCorrectionAtSaddle,
    HAdmissible.B, fragPermThirdWindowHAdmissible,
    fragPermThirdWindowSaddleSequence, fragPermThirdWindowSecondOrder,
    fragPermThirdWindowThirdOrder, fragPermThirdRobustCorrScale] using h

theorem fragPerm_count_over_factorial_thirdOrder :
    (fun n : ℕ =>
      fragPermSeries.coeff n / fragPermThirdOrderSaddleScale n -
        (1 + (fragPermSecondCorrectionAtSaddle n : ℂ) +
          (fragPermThirdCorrectionAtSaddle n : ℂ)))
      =o[atTop]
    (fun n : ℕ => (fragPermThirdRobustCorrScale (fragPermSaddleRadius n) : ℂ)) := by
  simpa [fragPermThirdOrderSeriesError] using
    fragPerm_coeff_thirdOrder_saddle_from_HAdmissible

end FragmentedPermHAdmissible
