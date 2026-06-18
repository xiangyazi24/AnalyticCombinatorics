import AnalyticCombinatorics.Ch8.SaddlePoint.SecondOrderHAdmissible
import AnalyticCombinatorics.Ch8.SaddlePoint.InvolutionHAdmissible

/-!
# Second-order saddle data for involutions

This file adds the second-order correction layer for
`exp (z + z^2 / 2)`.  The logarithmic saddle derivatives are
`b₃(r)=r+4r²` and `b₄(r)=r+8r²`.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval PowerSeries

set_option maxHeartbeats 800000

noncomputable section

namespace InvolutionHAdmissible

/-- Third logarithmic saddle derivative for involutions. -/
def involSaddleB3Real (r : ℝ) : ℝ :=
  r + 4 * r ^ 2

/-- Fourth logarithmic saddle derivative for involutions. -/
def involSaddleB4Real (r : ℝ) : ℝ :=
  r + 8 * r ^ 2

/-- Robust second-order correction scale for involutions. -/
def involSecondCorrScale (r : ℝ) : ℝ :=
  saddleCorrectionScale involSaddleBReal involSaddleB3Real involSaddleB4Real r

/-- Complex saddle scale used by the involution second-order statement. -/
def involSecondOrderSaddleScale (n : ℕ) : ℂ :=
  saddleScale involFun involSaddleRadius
    (fun n => involSaddleBReal (involSaddleRadius n)) n

/-- The EGF coefficient `I_n/n!` as a complex number. -/
def involCoeffC (n : ℕ) : ℂ :=
  (involCoeffR n : ℂ)

/-- The error after inserting the explicit involution correction `-1/(6n)`. -/
def involSecondOrderOneOverNError (n : ℕ) : ℂ :=
  involCoeffC n / involSecondOrderSaddleScale n -
    (1 - (1 : ℂ) / (6 * (n : ℂ)))

/-- The final involution second-order comparison scale. -/
def involOneOverNScale (n : ℕ) : ℂ :=
  ((1 : ℝ) / (n : ℝ) : ℂ)

lemma invol_saddleCorrection_eq {r : ℝ} (hr : r ≠ 0) :
    saddleCorrection involSaddleBReal involSaddleB3Real involSaddleB4Real r =
      -((16 * r ^ 2 + 5 * r + 1) / (12 * r * (1 + 2 * r) ^ 3)) := by
  unfold saddleCorrection involSaddleBReal involSaddleB3Real involSaddleB4Real
  field_simp [hr]
  ring

private lemma complex_isLittleO_of_norm_div_tendsto_zero_nat
    (u : ℕ → ℂ) (c : ℕ → ℝ)
    (hcpos : ∀ᶠ n in atTop, 0 < c n)
    (h : Tendsto (fun n : ℕ => ‖u n‖ / c n) atTop (𝓝 0)) :
    u =o[atTop] (fun n : ℕ => (c n : ℂ)) := by
  rw [isLittleO_iff_tendsto']
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    refine Tendsto.congr' ?_ h
    filter_upwards [hcpos] with n hcn
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcn]
  · filter_upwards [hcpos] with n hcn hzero
    exact (hcn.ne' (Complex.ofReal_eq_zero.mp hzero)).elim

lemma involSecondCorrScale_eq_rational {r : ℝ} (hr : 0 < r) :
    involSecondCorrScale r =
      (2 + 18 * r + 32 * r ^ 2) / (r * (1 + 2 * r) ^ 3) := by
  unfold involSecondCorrScale saddleCorrectionScale involSaddleBReal involSaddleB3Real
    involSaddleB4Real
  have h4 : 0 ≤ r + 8 * r ^ 2 := by positivity
  rw [abs_of_nonneg h4]
  field_simp [hr.ne']
  ring

lemma involSecondCorrScale_pos_eventually :
    ∀ᶠ r : ℝ in atTop, 0 < involSecondCorrScale r := by
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  unfold involSecondCorrScale saddleCorrectionScale involSaddleBReal involSaddleB3Real
    involSaddleB4Real
  positivity

lemma involSecondCorrScale_nonneg_eventually :
    ∀ᶠ r : ℝ in atTop, 0 ≤ involSecondCorrScale r :=
  involSecondCorrScale_pos_eventually.mono fun _ h => h.le

lemma involSecondCorrScale_le_rpow_eventually :
    ∀ᶠ r : ℝ in atTop, involSecondCorrScale r ≤ 100 * r ^ (-(2 : ℝ)) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  rw [involSecondCorrScale_eq_rational hrpos]
  rw [Real.rpow_neg hrpos.le]
  field_simp [hrpos.ne']
  have hr2_rpow : r ^ 2 = r ^ (2 : ℝ) := by
    exact (Real.rpow_natCast r 2).symm
  calc
    (2 + 18 * r + r ^ 2 * 32) * r ^ (2 : ℝ)
        = (2 + 18 * r + r ^ 2 * 32) * r ^ 2 := by rw [← hr2_rpow]
    _ = 2 * r ^ 2 + 18 * r ^ 3 + 32 * r ^ 4 := by ring
    _ ≤ 100 * r + 600 * r ^ 2 + 1200 * r ^ 3 + 800 * r ^ 4 := by
      have hdiff : 0 ≤ 100 * r + 598 * r ^ 2 + 1182 * r ^ 3 + 768 * r ^ 4 := by
        positivity
      nlinarith [hdiff]
    _ = r * (1 + 2 * r) ^ 3 * 100 := by ring

lemma involSecondCorrScale_lower_eventually :
    ∀ᶠ r : ℝ in atTop,
      (16 / 27 : ℝ) * r ^ (-(2 : ℝ)) ≤ involSecondCorrScale r := by
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  rw [involSecondCorrScale_eq_rational hrpos]
  rw [Real.rpow_neg hrpos.le]
  field_simp [hrpos.ne']
  have hr2_rpow : r ^ 2 = r ^ (2 : ℝ) := by
    exact (Real.rpow_natCast r 2).symm
  calc
    16 * r * (1 + 2 * r) ^ 3
        ≤ 27 * r ^ 2 * (2 + 18 * r + r ^ 2 * 32) := by
          ring_nf
          nlinarith [hr, mul_nonneg hrpos.le hrpos.le, show 0 ≤ r ^ 3 by positivity,
            show 0 ≤ r ^ 4 by positivity]
    _ = 27 * r ^ (2 : ℝ) * (2 + 18 * r + r ^ 2 * 32) := by rw [← hr2_rpow]

lemma involSecondCorrScale_tendsto_zero :
    Tendsto involSecondCorrScale atTop (𝓝 0) := by
  have hupper : Tendsto (fun r : ℝ => 100 * r ^ (-(2 : ℝ))) atTop (𝓝 0) := by
    simpa using
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2)).const_mul (100 : ℝ)
  exact squeeze_zero' involSecondCorrScale_nonneg_eventually
    involSecondCorrScale_le_rpow_eventually hupper

lemma involTailE_second_decay :
    Tendsto
      (fun r : ℝ =>
        Real.sqrt (2 * Real.pi * involSaddleBReal r) * involTailE r /
          involSecondCorrScale r)
      atTop (𝓝 0) := by
  have hupper :
      Tendsto
        (fun r : ℝ =>
          (Real.sqrt (6 * Real.pi) * r * involTailE r) /
            ((16 / 27 : ℝ) * r ^ (-(2 : ℝ))))
        atTop (𝓝 0) := by
    let c : ℝ := 1 / (2 * Real.pi ^ 2)
    have hc : 0 < c := by
      dsimp [c]
      positivity
    have hbase :
        Tendsto (fun y : ℝ => y ^ (12 : ℝ) * Real.exp (-c * y)) atTop (𝓝 0) :=
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (12 : ℝ) c hc
    have hy : Tendsto (fun r : ℝ => r ^ (1 / 4 : ℝ)) atTop atTop :=
      tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)
    have hcomp :
        Tendsto
          (fun r : ℝ =>
            (r ^ (1 / 4 : ℝ)) ^ (12 : ℝ) * Real.exp (-c * r ^ (1 / 4 : ℝ)))
          atTop (𝓝 0) := hbase.comp hy
    have hscaled :
        Tendsto
          (fun r : ℝ =>
            (Real.sqrt (6 * Real.pi) * (27 / 16 : ℝ)) *
              ((r ^ (1 / 4 : ℝ)) ^ (12 : ℝ) *
                Real.exp (-c * r ^ (1 / 4 : ℝ))))
          atTop (𝓝 0) := by
      simpa using hcomp.const_mul (Real.sqrt (6 * Real.pi) * (27 / 16 : ℝ))
    refine Tendsto.congr' ?_ hscaled
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    have hr0 : 0 ≤ r := hr.le
    have hrpow12 : (r ^ (1 / 4 : ℝ)) ^ (12 : ℝ) = r ^ 3 := by
      rw [← Real.rpow_mul hr0]
      norm_num [Real.rpow_natCast]
    unfold involTailE
    dsimp [c]
    rw [hrpow12]
    rw [Real.rpow_neg hr0]
    field_simp [hr.ne']
    exact (Real.rpow_natCast r 2).symm
  refine squeeze_zero' ?_ ?_ hupper
  · filter_upwards [eventually_ge_atTop (1 : ℝ), involSecondCorrScale_lower_eventually] with
      r hr hcl
    have hαpos : 0 < (16 / 27 : ℝ) * r ^ (-(2 : ℝ)) := by
      have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
      positivity
    have hcpos : 0 < involSecondCorrScale r := lt_of_lt_of_le hαpos hcl
    exact div_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) (by unfold involTailE; positivity)) hcpos.le
  · filter_upwards [eventually_ge_atTop (1 : ℝ), involSecondCorrScale_lower_eventually] with
      r hr hcl
    have hr0 : 0 ≤ r := le_trans zero_le_one hr
    have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
    have hαpos : 0 < (16 / 27 : ℝ) * r ^ (-(2 : ℝ)) := by positivity
    have hE_nonneg : 0 ≤ involTailE r := by
      unfold involTailE
      positivity
    have hB_le : involSaddleBReal r ≤ 3 * r ^ 2 := by
      unfold involSaddleBReal
      nlinarith [hr]
    have hsqrt :
        Real.sqrt (2 * Real.pi * involSaddleBReal r) ≤ Real.sqrt (6 * Real.pi) * r := by
      have hmul : 2 * Real.pi * involSaddleBReal r ≤ 6 * Real.pi * r ^ 2 := by
        calc
          2 * Real.pi * involSaddleBReal r
              ≤ 2 * Real.pi * (3 * r ^ 2) :=
                mul_le_mul_of_nonneg_left hB_le (by positivity)
          _ = 6 * Real.pi * r ^ 2 := by ring_nf
      calc
        Real.sqrt (2 * Real.pi * involSaddleBReal r)
            ≤ Real.sqrt (6 * Real.pi * r ^ 2) := Real.sqrt_le_sqrt hmul
        _ = Real.sqrt (6 * Real.pi) * r := by
          have h6pi : 0 ≤ 6 * Real.pi := by positivity
          rw [Real.sqrt_mul h6pi (r ^ 2)]
          rw [Real.sqrt_sq hr0]
    have hnum :
        Real.sqrt (2 * Real.pi * involSaddleBReal r) * involTailE r ≤
          Real.sqrt (6 * Real.pi) * r * involTailE r := by
      calc
        Real.sqrt (2 * Real.pi * involSaddleBReal r) * involTailE r
            ≤ (Real.sqrt (6 * Real.pi) * r) * involTailE r :=
              mul_le_mul_of_nonneg_right hsqrt hE_nonneg
        _ = Real.sqrt (6 * Real.pi) * r * involTailE r := by ring
    calc
      Real.sqrt (2 * Real.pi * involSaddleBReal r) * involTailE r /
          involSecondCorrScale r
          ≤ Real.sqrt (2 * Real.pi * involSaddleBReal r) * involTailE r /
              ((16 / 27 : ℝ) * r ^ (-(2 : ℝ))) :=
            div_le_div_of_nonneg_left (mul_nonneg (Real.sqrt_nonneg _) hE_nonneg) hαpos hcl
      _ ≤ (Real.sqrt (6 * Real.pi) * r * involTailE r) /
              ((16 / 27 : ℝ) * r ^ (-(2 : ℝ))) :=
            div_le_div_of_nonneg_right hnum hαpos.le

lemma invol_tail_second_uniform :
    ∃ E : ℝ → ℝ,
      (∀ᶠ r : ℝ in atTop, 0 ≤ E r) ∧
      Tendsto
        (fun r : ℝ => Real.sqrt (2 * Real.pi * involSaddleBReal r) * E r /
          involSecondCorrScale r)
        atTop (𝓝 0) ∧
      (∀ᶠ r : ℝ in atTop, ∀ n : ℕ, ∀ θ : ℝ,
        involSaddleDeltaReal r ≤ |θ| → |θ| ≤ Real.pi →
          ‖saddleGAt involFun r n θ‖ ≤ E r) := by
  exact ⟨involTailE, involTailE_nonneg_eventually, involTailE_second_decay,
    invol_tail_bound_eventually⟩

private def expLocalRemainderFifth (θ : ℝ) : ℂ :=
  ExpStirling.expLocalRemainder θ -
    ((((θ : ℂ) * Complex.I) ^ 3) / (((3 : ℕ).factorial : ℕ) : ℂ) +
      (((θ : ℂ) * Complex.I) ^ 4) / (((4 : ℕ).factorial : ℕ) : ℂ))

private lemma expLocalRemainderFifth_norm_le {θ : ℝ} (hθ : |θ| ≤ 2) :
    ‖expLocalRemainderFifth θ‖ ≤ Real.exp 2 * |θ| ^ 5 := by
  let u : ℂ := (θ : ℂ) * Complex.I
  have htail := Complex.norm_exp_sub_sum_le_norm_mul_exp u 5
  have hnorm : ‖u‖ = |θ| := by simp [u]
  have hleft :
      ExpStirling.expLocalRemainder θ -
          (u ^ 3 / (((3 : ℕ).factorial : ℕ) : ℂ) +
            u ^ 4 / (((4 : ℕ).factorial : ℕ) : ℂ)) =
        Complex.exp u - ∑ m ∈ Finset.range 5, u ^ m / (m.factorial : ℂ) := by
    simp [ExpStirling.expLocalRemainder, u, Finset.sum_range_succ]
    ring
  change
    ‖ExpStirling.expLocalRemainder θ -
        (u ^ 3 / (((3 : ℕ).factorial : ℕ) : ℂ) +
          u ^ 4 / (((4 : ℕ).factorial : ℕ) : ℂ))‖ ≤
      Real.exp 2 * |θ| ^ 5
  rw [hleft]
  calc
    ‖Complex.exp u - ∑ m ∈ Finset.range 5, u ^ m / (m.factorial : ℂ)‖
        ≤ ‖u‖ ^ 5 * Real.exp ‖u‖ := htail
    _ = |θ| ^ 5 * Real.exp |θ| := by rw [hnorm]
    _ ≤ |θ| ^ 5 * Real.exp 2 := by
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hθ)
        (pow_nonneg (abs_nonneg θ) 5)
    _ = Real.exp 2 * |θ| ^ 5 := by ring

private lemma involLocalExponent_split_fifth (r θ : ℝ) :
    involLocalExponent r θ =
      -Complex.I * ((involSaddleB3Real r : ℂ) / 6) * (θ : ℂ) ^ 3 +
        ((involSaddleB4Real r : ℂ) / 24) * (θ : ℂ) ^ 4 +
        (r : ℂ) * expLocalRemainderFifth θ +
        (((r ^ 2 / 2 : ℝ) : ℂ) * expLocalRemainderFifth (2 * θ)) := by
  unfold involLocalExponent expLocalRemainderFifth involSaddleB3Real involSaddleB4Real
  ring_nf
  simp [Complex.I_pow_three, Complex.I_pow_four]
  ring_nf

private def involScaledCubic (r x : ℝ) : ℂ :=
  -Complex.I *
    ((involSaddleB3Real r : ℂ) /
      (6 * (Real.sqrt (involSaddleBReal r) : ℂ) ^ 3)) * (x : ℂ) ^ 3

private def involScaledQuartic (r x : ℝ) : ℂ :=
  ((involSaddleB4Real r : ℂ) / (24 * (involSaddleBReal r : ℂ) ^ 2)) *
    (x : ℂ) ^ 4

private def involScaledRemainder (r x : ℝ) : ℂ :=
  (r : ℂ) * expLocalRemainderFifth (x / Real.sqrt (involSaddleBReal r)) +
    (((r ^ 2 / 2 : ℝ) : ℂ) *
      expLocalRemainderFifth (2 * (x / Real.sqrt (involSaddleBReal r))))

private lemma involLocalExponent_scaled_split {r x : ℝ}
    (hb : 0 < involSaddleBReal r) :
    involLocalExponent r (x / Real.sqrt (involSaddleBReal r)) =
      involScaledCubic r x + involScaledQuartic r x + involScaledRemainder r x := by
  have hsqrt_ne : (Real.sqrt (involSaddleBReal r) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hb).ne'
  rw [involLocalExponent_split_fifth]
  unfold involScaledCubic involScaledQuartic involScaledRemainder
  have hsqrt_sq :
      ((Real.sqrt (involSaddleBReal r) : ℂ) ^ 2) =
        (involSaddleBReal r : ℂ) := by
    exact_mod_cast (Real.sq_sqrt hb.le)
  have hsqrt_inv_pow4 :
      ((Real.sqrt (r + r ^ 2 * 2) : ℂ)⁻¹) ^ 4 =
        (↑r ^ 2 + ↑r ^ 3 * 4 + ↑r ^ 4 * 4 : ℂ)⁻¹ := by
    rw [inv_pow]
    congr 1
    have harg : r + r ^ 2 * 2 = involSaddleBReal r := by
      unfold involSaddleBReal
      ring
    calc
      (Real.sqrt (r + r ^ 2 * 2) : ℂ) ^ 4 =
          ((Real.sqrt (involSaddleBReal r) : ℂ) ^ 2) ^ 2 := by
            rw [harg]
            ring
      _ = (involSaddleBReal r : ℂ) ^ 2 := by rw [hsqrt_sq]
      _ = (↑r ^ 2 + ↑r ^ 3 * 4 + ↑r ^ 4 * 4 : ℂ) := by
        unfold involSaddleBReal
        exact_mod_cast (by ring : (r + 2 * r ^ 2) ^ 2 = r ^ 2 + r ^ 3 * 4 + r ^ 4 * 4)
  simp [Complex.ofReal_inv, div_eq_mul_inv]
  ring_nf
  rw [hsqrt_inv_pow4]
  ring

private lemma saddleSecondPoly_eq_scaled_terms {r x : ℝ}
    (hb : 0 < involSaddleBReal r) :
    saddleSecondPoly involSaddleBReal involSaddleB3Real involSaddleB4Real r x =
      1 + involScaledCubic r x + involScaledQuartic r x +
        (involScaledCubic r x) ^ 2 / 2 := by
  have hsqrt_sq :
      ((Real.sqrt (involSaddleBReal r) : ℂ) ^ 2) =
        (involSaddleBReal r : ℂ) := by
    exact_mod_cast (Real.sq_sqrt hb.le)
  have hsqrt_ne : (Real.sqrt (involSaddleBReal r) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hb).ne'
  have hb_ne : (involSaddleBReal r : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hb.ne'
  have hsqrt_pow6 :
      (Real.sqrt (involSaddleBReal r) : ℂ) ^ 6 =
        (involSaddleBReal r : ℂ) ^ 3 := by
    calc
      (Real.sqrt (involSaddleBReal r) : ℂ) ^ 6 =
          ((Real.sqrt (involSaddleBReal r) : ℂ) ^ 2) ^ 3 := by ring
      _ = (involSaddleBReal r : ℂ) ^ 3 := by rw [hsqrt_sq]
  unfold saddleSecondPoly involScaledCubic involScaledQuartic
  field_simp [hsqrt_ne, hb_ne]
  ring_nf
  rw [hsqrt_pow6, Complex.I_sq]
  norm_num [Complex.ofReal_pow]
  ring

private def involGaussianDom (x : ℝ) : ℝ :=
  Real.exp (-(x ^ 2) / 2) *
    (|x| ^ 5 + |x| ^ 7 + |x| ^ 8 + |x| ^ 9 + |x| ^ 10)

private lemma involGaussianDom_nonneg (x : ℝ) : 0 ≤ involGaussianDom x := by
  unfold involGaussianDom
  positivity

private lemma gaussian_abs_monomial_integrable (k : ℕ) :
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

private lemma involGaussianDom_integrable : Integrable involGaussianDom := by
  unfold involGaussianDom
  have hsum :
      Integrable
        ((((fun x : ℝ => Real.exp (-(x ^ 2) / 2) * |x| ^ 5) +
          (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * |x| ^ 7)) +
          (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * |x| ^ 8)) +
          ((fun x : ℝ => Real.exp (-(x ^ 2) / 2) * |x| ^ 9) +
            (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * |x| ^ 10))) :=
    (((gaussian_abs_monomial_integrable 5).add
      (gaussian_abs_monomial_integrable 7)).add
      (gaussian_abs_monomial_integrable 8)).add
      (((gaussian_abs_monomial_integrable 9).add
        (gaussian_abs_monomial_integrable 10)))
  convert hsum using 1
  ext x
  simp only [Pi.add_apply]
  ring_nf

private lemma involGaussianDom_integral_nonneg :
    0 ≤ ∫ x : ℝ, involGaussianDom x := by
  exact integral_nonneg (fun x => involGaussianDom_nonneg x)

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

private lemma invol_sqrtB_le_two_r {r : ℝ} (hr : 1 ≤ r) :
    Real.sqrt (involSaddleBReal r) ≤ 2 * r := by
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  have hmul : involSaddleBReal r ≤ (2 * r) ^ 2 := by
    unfold involSaddleBReal
    nlinarith [hr, sq_nonneg r]
  calc
    Real.sqrt (involSaddleBReal r) ≤ Real.sqrt ((2 * r) ^ 2) :=
      Real.sqrt_le_sqrt hmul
    _ = 2 * r := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (mul_nonneg (by norm_num) hr0)]

private lemma involScaledCubic_norm_le {r x : ℝ} (hr : 1 ≤ r) :
    ‖involScaledCubic r x‖ ≤ 10 * |x| ^ 3 / r := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hbpos : 0 < involSaddleBReal r := involSaddleBReal_pos_of_ge_one hr
  have hsqrt_pos : 0 < Real.sqrt (involSaddleBReal r) := Real.sqrt_pos.mpr hbpos
  have hsqrt_ge : r ≤ Real.sqrt (involSaddleBReal r) := invol_sqrtB_ge_r hr
  have hsqrt3_ge : r ^ 3 ≤ (Real.sqrt (involSaddleBReal r)) ^ 3 :=
    pow_le_pow_left₀ hrpos.le hsqrt_ge 3
  have hb3_nonneg : 0 ≤ involSaddleB3Real r := by
    unfold involSaddleB3Real
    nlinarith [hr, sq_nonneg r]
  have hb3_le : involSaddleB3Real r ≤ 5 * r ^ 2 := by
    unfold involSaddleB3Real
    nlinarith [hr]
  have hcoef :
      ‖(involSaddleB3Real r : ℂ) /
          (6 * (Real.sqrt (involSaddleBReal r) : ℂ) ^ 3)‖ ≤ 1 / r := by
    have hdenpos : 0 < 6 * (Real.sqrt (involSaddleBReal r)) ^ 3 := by positivity
    calc
      ‖(involSaddleB3Real r : ℂ) /
          (6 * (Real.sqrt (involSaddleBReal r) : ℂ) ^ 3)‖
          = involSaddleB3Real r /
              (6 * |Real.sqrt (involSaddleBReal r)| ^ 3) := by
            rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg hb3_nonneg]
            simp [norm_pow, Complex.norm_real, Real.norm_eq_abs]
      _ = involSaddleB3Real r /
              (6 * (Real.sqrt (involSaddleBReal r)) ^ 3) := by
            rw [abs_of_pos hsqrt_pos]
      _ ≤ (5 * r ^ 2) / (6 * r ^ 3) := by
        exact div_le_div₀ (by positivity) hb3_le (by positivity) (by nlinarith [hsqrt3_ge])
      _ ≤ 1 / r := by
        field_simp [hrpos.ne']
        nlinarith
  calc
    ‖involScaledCubic r x‖
        = ‖(involSaddleB3Real r : ℂ) /
            (6 * (Real.sqrt (involSaddleBReal r) : ℂ) ^ 3)‖ * |x| ^ 3 := by
          unfold involScaledCubic
          rw [norm_mul, norm_mul, norm_neg, norm_I, one_mul, norm_pow,
            Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (1 / r) * |x| ^ 3 :=
      mul_le_mul_of_nonneg_right hcoef (pow_nonneg (abs_nonneg x) 3)
    _ ≤ 10 * |x| ^ 3 / r := by
      field_simp [hrpos.ne']
      nlinarith [pow_nonneg (abs_nonneg x) 3]

private lemma involScaledQuartic_norm_le {r x : ℝ} (hr : 1 ≤ r) :
    ‖involScaledQuartic r x‖ ≤ 10 * |x| ^ 4 / r ^ 2 := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hbpos : 0 < involSaddleBReal r := involSaddleBReal_pos_of_ge_one hr
  have hb_ge : r ^ 2 ≤ involSaddleBReal r := by
    unfold involSaddleBReal
    nlinarith [sq_nonneg r]
  have hb4_nonneg : 0 ≤ involSaddleB4Real r := by
    unfold involSaddleB4Real
    nlinarith [hr, sq_nonneg r]
  have hb4_le : involSaddleB4Real r ≤ 9 * r ^ 2 := by
    unfold involSaddleB4Real
    nlinarith [hr]
  have hb_sq_ge : r ^ 4 ≤ (involSaddleBReal r) ^ 2 := by
    calc
      r ^ 4 = (r ^ 2) ^ 2 := by ring
      _ ≤ (involSaddleBReal r) ^ 2 :=
        pow_le_pow_left₀ (sq_nonneg r) hb_ge 2
  have hcoef :
      ‖(involSaddleB4Real r : ℂ) / (24 * (involSaddleBReal r : ℂ) ^ 2)‖ ≤
        1 / r ^ 2 := by
    calc
      ‖(involSaddleB4Real r : ℂ) / (24 * (involSaddleBReal r : ℂ) ^ 2)‖
          = involSaddleB4Real r / (24 * ‖(involSaddleBReal r : ℂ)‖ ^ 2) := by
            rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg hb4_nonneg]
            simp [norm_pow]
      _ = involSaddleB4Real r / (24 * (involSaddleBReal r) ^ 2) := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hbpos]
      _ ≤ (9 * r ^ 2) / (24 * r ^ 4) := by
        exact div_le_div₀ (by positivity) hb4_le (by positivity) (by nlinarith [hb_sq_ge])
      _ ≤ 1 / r ^ 2 := by
        have hr2pos : 0 < r ^ 2 := sq_pos_of_pos hrpos
        field_simp [hrpos.ne', hr2pos.ne']
        nlinarith
  calc
    ‖involScaledQuartic r x‖
        = ‖(involSaddleB4Real r : ℂ) /
            (24 * (involSaddleBReal r : ℂ) ^ 2)‖ * |x| ^ 4 := by
          unfold involScaledQuartic
          rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (1 / r ^ 2) * |x| ^ 4 :=
      mul_le_mul_of_nonneg_right hcoef (pow_nonneg (abs_nonneg x) 4)
    _ ≤ 10 * |x| ^ 4 / r ^ 2 := by
      have hr2pos : 0 < r ^ 2 := sq_pos_of_pos hrpos
      field_simp [hr2pos.ne']
      nlinarith [pow_nonneg (abs_nonneg x) 4]

private lemma involScaledRemainder_norm_le {r x : ℝ}
    (hr : 1 ≤ r) (hθ : |x / Real.sqrt (involSaddleBReal r)| ≤ 1) :
    ‖involScaledRemainder r x‖ ≤ 100 * Real.exp 2 * |x| ^ 5 / r ^ 3 := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hbpos : 0 < involSaddleBReal r := involSaddleBReal_pos_of_ge_one hr
  have hsqrt_pos : 0 < Real.sqrt (involSaddleBReal r) := Real.sqrt_pos.mpr hbpos
  have hsqrt_ge : r ≤ Real.sqrt (involSaddleBReal r) := invol_sqrtB_ge_r hr
  have hθ_two : |2 * (x / Real.sqrt (involSaddleBReal r))| ≤ 2 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  have hθ_abs_le : |x / Real.sqrt (involSaddleBReal r)| ≤ |x| / r := by
    rw [abs_div, abs_of_pos hsqrt_pos]
    exact div_le_div_of_nonneg_left (abs_nonneg x) hrpos hsqrt_ge
  have hθ5_le : |x / Real.sqrt (involSaddleBReal r)| ^ 5 ≤ (|x| / r) ^ 5 :=
    pow_le_pow_left₀ (abs_nonneg _) hθ_abs_le 5
  have hrem1 := expLocalRemainderFifth_norm_le (by linarith : |x / Real.sqrt (involSaddleBReal r)| ≤ 2)
  have hrem2 := expLocalRemainderFifth_norm_le hθ_two
  have hmain :
      ‖involScaledRemainder r x‖ ≤
        r * (Real.exp 2 * (|x| / r) ^ 5) +
          (r ^ 2 / 2) * (Real.exp 2 * (2 * (|x| / r)) ^ 5) := by
    unfold involScaledRemainder
    calc
      ‖(r : ℂ) * expLocalRemainderFifth (x / Real.sqrt (involSaddleBReal r)) +
          (((r ^ 2 / 2 : ℝ) : ℂ) *
            expLocalRemainderFifth (2 * (x / Real.sqrt (involSaddleBReal r))))‖
          ≤ ‖(r : ℂ) * expLocalRemainderFifth (x / Real.sqrt (involSaddleBReal r))‖ +
              ‖(((r ^ 2 / 2 : ℝ) : ℂ) *
                expLocalRemainderFifth (2 * (x / Real.sqrt (involSaddleBReal r))))‖ :=
            norm_add_le _ _
      _ ≤ r * (Real.exp 2 * (|x| / r) ^ 5) +
            (r ^ 2 / 2) * (Real.exp 2 * |2 * (x / Real.sqrt (involSaddleBReal r))| ^ 5) := by
          gcongr
          · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos]
            exact mul_le_mul_of_nonneg_left
              (hrem1.trans (mul_le_mul_of_nonneg_left hθ5_le (Real.exp_pos 2).le))
              hrpos.le
          · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
            have hcoef : 0 ≤ r ^ 2 / 2 := by positivity
            rw [abs_of_nonneg hcoef]
            exact mul_le_mul_of_nonneg_left hrem2 hcoef
      _ ≤ r * (Real.exp 2 * (|x| / r) ^ 5) +
            (r ^ 2 / 2) * (Real.exp 2 * (2 * (|x| / r)) ^ 5) := by
          gcongr
          rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
          exact mul_le_mul_of_nonneg_left hθ_abs_le (by norm_num)
  calc
    ‖involScaledRemainder r x‖
        ≤ r * (Real.exp 2 * (|x| / r) ^ 5) +
          (r ^ 2 / 2) * (Real.exp 2 * (2 * (|x| / r)) ^ 5) := hmain
    _ ≤ 100 * Real.exp 2 * |x| ^ 5 / r ^ 3 := by
      field_simp [hrpos.ne']
      ring_nf
      nlinarith [Real.exp_pos 2, pow_nonneg (abs_nonneg x) 5]

private lemma complex_exp_second_error_bound (C Q R W : ℂ)
    (hW : W = C + Q + R) (hWnorm : ‖W‖ ≤ 1) :
    ‖Complex.exp W - (1 + C + Q + C ^ 2 / 2)‖ ≤
      Real.exp 1 * ‖W‖ ^ 3 + ‖R‖ +
        (‖Q‖ + ‖R‖) * (2 * ‖C‖ + ‖Q‖ + ‖R‖) := by
  have hsum :
      (∑ m ∈ Finset.range 3, W ^ m / (m.factorial : ℂ)) =
        1 + W + W ^ 2 / 2 := by
    simp [Finset.sum_range_succ]
  have htail :
      ‖Complex.exp W - (1 + W + W ^ 2 / 2)‖ ≤ Real.exp 1 * ‖W‖ ^ 3 := by
    calc
      ‖Complex.exp W - (1 + W + W ^ 2 / 2)‖ =
          ‖Complex.exp W - ∑ m ∈ Finset.range 3, W ^ m / (m.factorial : ℂ)‖ := by
            rw [hsum]
      _ ≤ ‖W‖ ^ 3 * Real.exp ‖W‖ :=
        Complex.norm_exp_sub_sum_le_norm_mul_exp W 3
      _ ≤ ‖W‖ ^ 3 * Real.exp 1 :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hWnorm) (pow_nonneg (norm_nonneg W) 3)
      _ = Real.exp 1 * ‖W‖ ^ 3 := by ring
  have hdecomp :
      Complex.exp W - (1 + C + Q + C ^ 2 / 2) =
        (Complex.exp W - (1 + W + W ^ 2 / 2)) +
          (R + (W ^ 2 - C ^ 2) / 2) := by
    rw [hW]
    ring
  rw [hdecomp]
  calc
    ‖(Complex.exp W - (1 + W + W ^ 2 / 2)) + (R + (W ^ 2 - C ^ 2) / 2)‖
        ≤ ‖Complex.exp W - (1 + W + W ^ 2 / 2)‖ +
            ‖R + (W ^ 2 - C ^ 2) / 2‖ := norm_add_le _ _
    _ ≤ Real.exp 1 * ‖W‖ ^ 3 + ‖R + (W ^ 2 - C ^ 2) / 2‖ :=
      add_le_add htail (le_refl _)
    _ ≤ Real.exp 1 * ‖W‖ ^ 3 + (‖R‖ + ‖(W ^ 2 - C ^ 2) / 2‖) := by
      exact add_le_add (le_refl _) (norm_add_le _ _)
    _ ≤ Real.exp 1 * ‖W‖ ^ 3 + (‖R‖ + ‖W ^ 2 - C ^ 2‖) := by
      have hhalf : ‖(W ^ 2 - C ^ 2) / 2‖ ≤ ‖W ^ 2 - C ^ 2‖ := by
        rw [norm_div, Complex.norm_ofNat]
        norm_num
      exact add_le_add (le_refl _) (add_le_add_right hhalf _)
    _ ≤ Real.exp 1 * ‖W‖ ^ 3 + ‖R‖ +
          (‖Q‖ + ‖R‖) * (2 * ‖C‖ + ‖Q‖ + ‖R‖) := by
      have hsq :
          W ^ 2 - C ^ 2 = (Q + R) * (2 * C + Q + R) := by
        rw [hW]
        ring
      have hprod :
          ‖W ^ 2 - C ^ 2‖ ≤ (‖Q‖ + ‖R‖) * (2 * ‖C‖ + ‖Q‖ + ‖R‖) := by
        rw [hsq]
        calc
          ‖(Q + R) * (2 * C + Q + R)‖ =
              ‖Q + R‖ * ‖2 * C + Q + R‖ := by rw [norm_mul]
          _ ≤ (‖Q‖ + ‖R‖) * (2 * ‖C‖ + ‖Q‖ + ‖R‖) := by
            have hQR : ‖Q + R‖ ≤ ‖Q‖ + ‖R‖ := norm_add_le _ _
            have h2C : ‖(2 : ℂ) * C‖ = 2 * ‖C‖ := by
              rw [norm_mul, Complex.norm_ofNat]
            have hCQR : ‖2 * C + Q + R‖ ≤ 2 * ‖C‖ + ‖Q‖ + ‖R‖ := by
              calc
                ‖2 * C + Q + R‖ ≤ ‖2 * C + Q‖ + ‖R‖ := norm_add_le _ _
                _ ≤ (‖2 * C‖ + ‖Q‖) + ‖R‖ :=
                  add_le_add (norm_add_le _ _) (le_refl _)
                _ = 2 * ‖C‖ + ‖Q‖ + ‖R‖ := by rw [h2C]
            exact mul_le_mul hQR hCQR (norm_nonneg _) (by positivity)
      nlinarith [hprod]

private def involLocalL1Const : ℝ :=
  100 * Real.exp 2 + Real.exp 1 * (1000 * Real.exp 2) ^ 3 +
    (200 + 3000 * Real.exp 2 + 10000 * (Real.exp 2) ^ 2)

private lemma involLocalL1Const_pos : 0 < involLocalL1Const := by
  unfold involLocalL1Const
  positivity

private lemma invol_local_integrand_bound {r x : ℝ}
    (hr : 1 ≤ r)
    (hθ : |x / Real.sqrt (involSaddleBReal r)| ≤ 1)
    (hx2r : |x| ≤ 2 * r)
    (hWnorm : ‖involLocalExponent r (x / Real.sqrt (involSaddleBReal r))‖ ≤ 1) :
    ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleLocalRatio involFun involSaddleAReal involSaddleBReal r
            (x / Real.sqrt (involSaddleBReal r)) -
          saddleSecondPoly involSaddleBReal involSaddleB3Real involSaddleB4Real r x)‖
      ≤ involLocalL1Const * involGaussianDom x / r ^ 3 := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hbpos : 0 < involSaddleBReal r := involSaddleBReal_pos_of_ge_one hr
  let C : ℂ := involScaledCubic r x
  let Q : ℂ := involScaledQuartic r x
  let R : ℂ := involScaledRemainder r x
  let W : ℂ := involLocalExponent r (x / Real.sqrt (involSaddleBReal r))
  have hWsplit : W = C + Q + R := by
    dsimp [W, C, Q, R]
    exact involLocalExponent_scaled_split hbpos
  have hP :
      saddleSecondPoly involSaddleBReal involSaddleB3Real involSaddleB4Real r x =
        1 + C + Q + C ^ 2 / 2 := by
    dsimp [C, Q]
    exact saddleSecondPoly_eq_scaled_terms hbpos
  have herr := complex_exp_second_error_bound C Q R W hWsplit (by simpa [W] using hWnorm)
  have hC : ‖C‖ ≤ 10 * |x| ^ 3 / r := by
    dsimp [C]
    exact involScaledCubic_norm_le hr
  have hQ : ‖Q‖ ≤ 10 * |x| ^ 4 / r ^ 2 := by
    dsimp [Q]
    exact involScaledQuartic_norm_le hr
  have hR : ‖R‖ ≤ 100 * Real.exp 2 * |x| ^ 5 / r ^ 3 := by
    dsimp [R]
    exact involScaledRemainder_norm_le hr hθ
  have hy_nonneg : 0 ≤ |x| := abs_nonneg x
  have hr2pos : 0 < r ^ 2 := sq_pos_of_pos hrpos
  have hr3pos : 0 < r ^ 3 := by positivity
  have hy2_le : |x| ^ 2 ≤ (2 * r) ^ 2 :=
    (sq_le_sq₀ hy_nonneg (mul_nonneg (by norm_num) hrpos.le)).mpr hx2r
  have hQ_cubic : 10 * |x| ^ 4 / r ^ 2 ≤ 20 * |x| ^ 3 / r := by
    have hmul : 10 * |x| ^ 3 * |x| ≤ 10 * |x| ^ 3 * (2 * r) :=
      mul_le_mul_of_nonneg_left hx2r (by positivity)
    field_simp [hrpos.ne', hr2pos.ne']
    nlinarith [hmul]
  have hR_cubic :
      100 * Real.exp 2 * |x| ^ 5 / r ^ 3 ≤
        400 * Real.exp 2 * |x| ^ 3 / r := by
    field_simp [hrpos.ne', hr2pos.ne', hr3pos.ne']
    nlinarith [hy2_le, Real.exp_pos 2, pow_nonneg hy_nonneg 3]
  have hexp2_ge_one : 1 ≤ Real.exp 2 := by
    calc
      (1 : ℝ) = Real.exp 0 := by rw [Real.exp_zero]
      _ ≤ Real.exp 2 := Real.exp_le_exp.mpr (by norm_num : (0 : ℝ) ≤ 2)
  have hWpoly : ‖W‖ ≤ 1000 * Real.exp 2 * |x| ^ 3 / r := by
    calc
      ‖W‖ = ‖C + Q + R‖ := by rw [hWsplit]
      _ ≤ ‖C‖ + ‖Q‖ + ‖R‖ := by
        calc
          ‖C + Q + R‖ ≤ ‖C + Q‖ + ‖R‖ := norm_add_le _ _
          _ ≤ (‖C‖ + ‖Q‖) + ‖R‖ := add_le_add (norm_add_le _ _) (le_refl _)
          _ = ‖C‖ + ‖Q‖ + ‖R‖ := by ring
      _ ≤ 10 * |x| ^ 3 / r + 10 * |x| ^ 4 / r ^ 2 +
            100 * Real.exp 2 * |x| ^ 5 / r ^ 3 := by
        exact add_le_add (add_le_add hC hQ) hR
      _ ≤ 10 * |x| ^ 3 / r + 20 * |x| ^ 3 / r +
            400 * Real.exp 2 * |x| ^ 3 / r := by
        exact add_le_add (add_le_add (le_refl _) hQ_cubic) hR_cubic
      _ ≤ 1000 * Real.exp 2 * |x| ^ 3 / r := by
        field_simp [hrpos.ne']
        nlinarith [hexp2_ge_one, pow_nonneg hy_nonneg 3]
  have hWcube :
      Real.exp 1 * ‖W‖ ^ 3 ≤
        Real.exp 1 * (1000 * Real.exp 2) ^ 3 * |x| ^ 9 / r ^ 3 := by
    have hpow := pow_le_pow_left₀ (norm_nonneg W) hWpoly 3
    calc
      Real.exp 1 * ‖W‖ ^ 3
          ≤ Real.exp 1 * (1000 * Real.exp 2 * |x| ^ 3 / r) ^ 3 :=
            mul_le_mul_of_nonneg_left hpow (Real.exp_pos 1).le
      _ = Real.exp 1 * (1000 * Real.exp 2) ^ 3 * |x| ^ 9 / r ^ 3 := by
        field_simp [hrpos.ne']
  have hprod_bound :
      (10 * |x| ^ 4 / r ^ 2 + 100 * Real.exp 2 * |x| ^ 5 / r ^ 3) *
          (2 * (10 * |x| ^ 3 / r) + 10 * |x| ^ 4 / r ^ 2 +
            100 * Real.exp 2 * |x| ^ 5 / r ^ 3)
        ≤ (200 + 3000 * Real.exp 2 + 10000 * (Real.exp 2) ^ 2) *
            (|x| ^ 7 + |x| ^ 8 + |x| ^ 9 + |x| ^ 10) / r ^ 3 := by
    let D : ℝ := 200 + 3000 * Real.exp 2 + 10000 * (Real.exp 2) ^ 2
    have hD : 0 ≤ D := by dsimp [D]; positivity
    have hr_le_sq : r ≤ r ^ 2 := by nlinarith [hr, sq_nonneg r]
    have hr_sq_le_cu : r ^ 2 ≤ r ^ 3 := by
      nlinarith [hr, sq_nonneg r, show 0 ≤ r ^ 3 by positivity]
    have hr3_le_r4 : r ^ 3 ≤ r ^ 4 := by
      nlinarith [hr, hr_le_sq, hr_sq_le_cu, show 0 ≤ r ^ 4 by positivity]
    have hr3_le_r5 : r ^ 3 ≤ r ^ 5 := by
      nlinarith [hr, hr_le_sq, hr_sq_le_cu, hr3_le_r4, show 0 ≤ r ^ 5 by positivity]
    have hr3_le_r6 : r ^ 3 ≤ r ^ 6 := by
      nlinarith [hr, hr_le_sq, hr_sq_le_cu, hr3_le_r4, hr3_le_r5,
        show 0 ≤ r ^ 6 by positivity]
    have hD200 : 200 ≤ D := by
      have hnon : 0 ≤ 3000 * Real.exp 2 + 10000 * (Real.exp 2) ^ 2 := by positivity
      dsimp [D]
      calc
        (200 : ℝ) ≤ 200 + (3000 * Real.exp 2 + 10000 * (Real.exp 2) ^ 2) :=
          le_add_of_nonneg_right hnon
        _ = 200 + 3000 * Real.exp 2 + 10000 * (Real.exp 2) ^ 2 := by ring
    have hD8 : 100 + 2000 * Real.exp 2 ≤ D := by
      have hnon : 0 ≤ 100 + 1000 * Real.exp 2 + 10000 * (Real.exp 2) ^ 2 := by
        positivity
      dsimp [D]
      calc
        100 + 2000 * Real.exp 2
            ≤ 100 + 2000 * Real.exp 2 +
                (100 + 1000 * Real.exp 2 + 10000 * (Real.exp 2) ^ 2) :=
          le_add_of_nonneg_right hnon
        _ = 200 + 3000 * Real.exp 2 + 10000 * (Real.exp 2) ^ 2 := by ring
    have hD9 : 2000 * Real.exp 2 ≤ D := by
      have hnon : 0 ≤ 200 + 1000 * Real.exp 2 + 10000 * (Real.exp 2) ^ 2 := by
        positivity
      dsimp [D]
      calc
        2000 * Real.exp 2
            ≤ 2000 * Real.exp 2 +
                (200 + 1000 * Real.exp 2 + 10000 * (Real.exp 2) ^ 2) :=
          le_add_of_nonneg_right hnon
        _ = 200 + 3000 * Real.exp 2 + 10000 * (Real.exp 2) ^ 2 := by ring
    have hD10 : 10000 * (Real.exp 2) ^ 2 ≤ D := by
      have hnon : 0 ≤ 200 + 3000 * Real.exp 2 := by positivity
      dsimp [D]
      calc
        10000 * (Real.exp 2) ^ 2
            ≤ 10000 * (Real.exp 2) ^ 2 + (200 + 3000 * Real.exp 2) :=
          le_add_of_nonneg_right hnon
        _ = 200 + 3000 * Real.exp 2 + 10000 * (Real.exp 2) ^ 2 := by ring
    have hexpand :
        (10 * |x| ^ 4 / r ^ 2 + 100 * Real.exp 2 * |x| ^ 5 / r ^ 3) *
            (2 * (10 * |x| ^ 3 / r) + 10 * |x| ^ 4 / r ^ 2 +
              100 * Real.exp 2 * |x| ^ 5 / r ^ 3) =
          200 * |x| ^ 7 / r ^ 3 +
            (100 + 2000 * Real.exp 2) * |x| ^ 8 / r ^ 4 +
            2000 * Real.exp 2 * |x| ^ 9 / r ^ 5 +
            10000 * (Real.exp 2) ^ 2 * |x| ^ 10 / r ^ 6 := by
      field_simp [hrpos.ne']
      ring
    rw [hexpand]
    have h7 : 200 * |x| ^ 7 / r ^ 3 ≤ D * |x| ^ 7 / r ^ 3 := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hD200 (pow_nonneg hy_nonneg 7)) hr3pos.le
    have h8 : (100 + 2000 * Real.exp 2) * |x| ^ 8 / r ^ 4 ≤
        D * |x| ^ 8 / r ^ 3 := by
      calc
        (100 + 2000 * Real.exp 2) * |x| ^ 8 / r ^ 4
            ≤ D * |x| ^ 8 / r ^ 4 :=
              div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_right hD8 (pow_nonneg hy_nonneg 8))
                (by positivity)
        _ ≤ D * |x| ^ 8 / r ^ 3 :=
              div_le_div_of_nonneg_left
                (mul_nonneg hD (pow_nonneg hy_nonneg 8)) hr3pos hr3_le_r4
    have h9 : 2000 * Real.exp 2 * |x| ^ 9 / r ^ 5 ≤
        D * |x| ^ 9 / r ^ 3 := by
      calc
        2000 * Real.exp 2 * |x| ^ 9 / r ^ 5
            ≤ D * |x| ^ 9 / r ^ 5 :=
              div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_right hD9 (pow_nonneg hy_nonneg 9))
                (by positivity)
        _ ≤ D * |x| ^ 9 / r ^ 3 :=
              div_le_div_of_nonneg_left
                (mul_nonneg hD (pow_nonneg hy_nonneg 9)) hr3pos hr3_le_r5
    have h10 : 10000 * (Real.exp 2) ^ 2 * |x| ^ 10 / r ^ 6 ≤
        D * |x| ^ 10 / r ^ 3 := by
      calc
        10000 * (Real.exp 2) ^ 2 * |x| ^ 10 / r ^ 6
            ≤ D * |x| ^ 10 / r ^ 6 :=
              div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_right hD10 (pow_nonneg hy_nonneg 10))
                (by positivity)
        _ ≤ D * |x| ^ 10 / r ^ 3 :=
              div_le_div_of_nonneg_left
                (mul_nonneg hD (pow_nonneg hy_nonneg 10)) hr3pos hr3_le_r6
    calc
      200 * |x| ^ 7 / r ^ 3 +
            (100 + 2000 * Real.exp 2) * |x| ^ 8 / r ^ 4 +
            2000 * Real.exp 2 * |x| ^ 9 / r ^ 5 +
            10000 * (Real.exp 2) ^ 2 * |x| ^ 10 / r ^ 6
          ≤ D * |x| ^ 7 / r ^ 3 + D * |x| ^ 8 / r ^ 3 +
              D * |x| ^ 9 / r ^ 3 + D * |x| ^ 10 / r ^ 3 := by
            exact add_le_add (add_le_add (add_le_add h7 h8) h9) h10
      _ = D * (|x| ^ 7 + |x| ^ 8 + |x| ^ 9 + |x| ^ 10) / r ^ 3 := by
        ring
  have hquad :
      (‖Q‖ + ‖R‖) * (2 * ‖C‖ + ‖Q‖ + ‖R‖)
        ≤ (200 + 3000 * Real.exp 2 + 10000 * (Real.exp 2) ^ 2) *
            (|x| ^ 7 + |x| ^ 8 + |x| ^ 9 + |x| ^ 10) / r ^ 3 := by
    have hQR :
        ‖Q‖ + ‖R‖ ≤
          10 * |x| ^ 4 / r ^ 2 + 100 * Real.exp 2 * |x| ^ 5 / r ^ 3 :=
      add_le_add hQ hR
    have hCQR :
        2 * ‖C‖ + ‖Q‖ + ‖R‖ ≤
          2 * (10 * |x| ^ 3 / r) + 10 * |x| ^ 4 / r ^ 2 +
            100 * Real.exp 2 * |x| ^ 5 / r ^ 3 := by
      exact add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left hC (by norm_num : (0 : ℝ) ≤ 2)) hQ) hR
    have hQR_nonneg :
        0 ≤ 10 * |x| ^ 4 / r ^ 2 + 100 * Real.exp 2 * |x| ^ 5 / r ^ 3 := by
      positivity
    exact (mul_le_mul hQR hCQR (by positivity) hQR_nonneg).trans hprod_bound
  have hdiff :
      ‖Complex.exp W - (1 + C + Q + C ^ 2 / 2)‖ ≤
        involLocalL1Const *
          (|x| ^ 5 + |x| ^ 7 + |x| ^ 8 + |x| ^ 9 + |x| ^ 10) / r ^ 3 := by
    calc
      ‖Complex.exp W - (1 + C + Q + C ^ 2 / 2)‖
          ≤ Real.exp 1 * ‖W‖ ^ 3 + ‖R‖ +
              (‖Q‖ + ‖R‖) * (2 * ‖C‖ + ‖Q‖ + ‖R‖) := herr
      _ ≤ Real.exp 1 * (1000 * Real.exp 2) ^ 3 * |x| ^ 9 / r ^ 3 +
            100 * Real.exp 2 * |x| ^ 5 / r ^ 3 +
            (200 + 3000 * Real.exp 2 + 10000 * (Real.exp 2) ^ 2) *
              (|x| ^ 7 + |x| ^ 8 + |x| ^ 9 + |x| ^ 10) / r ^ 3 := by
        exact add_le_add (add_le_add hWcube hR) hquad
      _ ≤ involLocalL1Const *
            (|x| ^ 5 + |x| ^ 7 + |x| ^ 8 + |x| ^ 9 + |x| ^ 10) / r ^ 3 := by
        let A : ℝ := 100 * Real.exp 2
        let B : ℝ := Real.exp 1 * (1000 * Real.exp 2) ^ 3
        let D : ℝ := 200 + 3000 * Real.exp 2 + 10000 * (Real.exp 2) ^ 2
        let S : ℝ := |x| ^ 5 + |x| ^ 7 + |x| ^ 8 + |x| ^ 9 + |x| ^ 10
        let T : ℝ := |x| ^ 7 + |x| ^ 8 + |x| ^ 9 + |x| ^ 10
        have hA : 0 ≤ A := by dsimp [A]; positivity
        have hB : 0 ≤ B := by dsimp [B]; positivity
        have hD : 0 ≤ D := by dsimp [D]; positivity
        have hy5S : |x| ^ 5 ≤ S := by
          dsimp [S]
          have hrest : 0 ≤ |x| ^ 7 + |x| ^ 8 + |x| ^ 9 + |x| ^ 10 := by
            exact add_nonneg (add_nonneg (add_nonneg
              (pow_nonneg hy_nonneg 7) (pow_nonneg hy_nonneg 8))
              (pow_nonneg hy_nonneg 9)) (pow_nonneg hy_nonneg 10)
          calc
            |x| ^ 5 ≤ |x| ^ 5 + (|x| ^ 7 + |x| ^ 8 + |x| ^ 9 + |x| ^ 10) :=
              le_add_of_nonneg_right hrest
            _ = |x| ^ 5 + |x| ^ 7 + |x| ^ 8 + |x| ^ 9 + |x| ^ 10 := by ring
        have hy9S : |x| ^ 9 ≤ S := by
          dsimp [S]
          have hrest : 0 ≤ |x| ^ 5 + |x| ^ 7 + |x| ^ 8 + |x| ^ 10 := by
            exact add_nonneg (add_nonneg (add_nonneg
              (pow_nonneg hy_nonneg 5) (pow_nonneg hy_nonneg 7))
              (pow_nonneg hy_nonneg 8)) (pow_nonneg hy_nonneg 10)
          calc
            |x| ^ 9 ≤ (|x| ^ 5 + |x| ^ 7 + |x| ^ 8 + |x| ^ 10) + |x| ^ 9 :=
              le_add_of_nonneg_left hrest
            _ = |x| ^ 5 + |x| ^ 7 + |x| ^ 8 + |x| ^ 9 + |x| ^ 10 := by ring
        have hTS : T ≤ S := by
          dsimp [T, S]
          have h5 : 0 ≤ |x| ^ 5 := pow_nonneg hy_nonneg 5
          calc
            |x| ^ 7 + |x| ^ 8 + |x| ^ 9 + |x| ^ 10
                ≤ |x| ^ 5 + (|x| ^ 7 + |x| ^ 8 + |x| ^ 9 + |x| ^ 10) :=
                  le_add_of_nonneg_left h5
            _ = |x| ^ 5 + |x| ^ 7 + |x| ^ 8 + |x| ^ 9 + |x| ^ 10 := by abel
        change B * |x| ^ 9 / r ^ 3 + A * |x| ^ 5 / r ^ 3 + D * T / r ^ 3 ≤
          (A + B + D) * S / r ^ 3
        have hnum :
            B * |x| ^ 9 + A * |x| ^ 5 + D * T ≤ (A + B + D) * S := by
          calc
            B * |x| ^ 9 + A * |x| ^ 5 + D * T
                ≤ B * S + A * S + D * S := by
                  exact add_le_add (add_le_add
                    (mul_le_mul_of_nonneg_left hy9S hB)
                    (mul_le_mul_of_nonneg_left hy5S hA))
                    (mul_le_mul_of_nonneg_left hTS hD)
            _ = (A + B + D) * S := by ring
        calc
          B * |x| ^ 9 / r ^ 3 + A * |x| ^ 5 / r ^ 3 + D * T / r ^ 3
              = (B * |x| ^ 9 + A * |x| ^ 5 + D * T) / r ^ 3 := by ring
          _ ≤ ((A + B + D) * S) / r ^ 3 :=
            div_le_div_of_nonneg_right hnum hr3pos.le
          _ = (A + B + D) * S / r ^ 3 := by rfl
  rw [invol_saddleLocalRatio_eq]
  rw [hP]
  change
    ‖Complex.exp (-(x ^ 2) / 2) *
        (Complex.exp W - (1 + C + Q + C ^ 2 / 2))‖ ≤
      involLocalL1Const * involGaussianDom x / r ^ 3
  rw [norm_mul]
  have hgauss :
      ‖Complex.exp (-(x ^ 2) / 2)‖ = Real.exp (-(x ^ 2) / 2) := by
    rw [Complex.norm_exp]
    congr 1
    simp [pow_two]
  rw [hgauss]
  unfold involGaussianDom
  calc
    Real.exp (-(x ^ 2) / 2) * ‖Complex.exp W - (1 + C + Q + C ^ 2 / 2)‖
        ≤ Real.exp (-(x ^ 2) / 2) *
          (involLocalL1Const *
            (|x| ^ 5 + |x| ^ 7 + |x| ^ 8 + |x| ^ 9 + |x| ^ 10) / r ^ 3) :=
        mul_le_mul_of_nonneg_left hdiff (Real.exp_pos _).le
    _ = involLocalL1Const *
          (Real.exp (-(x ^ 2) / 2) *
            (|x| ^ 5 + |x| ^ 7 + |x| ^ 8 + |x| ^ 9 + |x| ^ 10)) / r ^ 3 := by
      ring

private lemma invol_local_integrand_continuous (r : ℝ) :
    Continuous fun x : ℝ =>
      ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleLocalRatio involFun involSaddleAReal involSaddleBReal r
            (x / Real.sqrt (involSaddleBReal r)) -
          saddleSecondPoly involSaddleBReal involSaddleB3Real involSaddleB4Real r x)‖ := by
  have h :
      Continuous fun x : ℝ =>
        ‖Complex.exp (-(x ^ 2) / 2) *
          (Complex.exp (involLocalExponent r (x / Real.sqrt (involSaddleBReal r))) -
            saddleSecondPoly involSaddleBReal involSaddleB3Real involSaddleB4Real r x)‖ := by
    unfold involLocalExponent ExpStirling.expLocalRemainder saddleSecondPoly
    fun_prop
  simpa [invol_saddleLocalRatio_eq] using h

private lemma involGaussianDom_continuous : Continuous involGaussianDom := by
  unfold involGaussianDom
  fun_prop

private lemma involGaussianDom_window_le_integral {L : ℝ} (hL : 0 ≤ L) :
    (∫ x in -L..L, involGaussianDom x) ≤ ∫ x : ℝ, involGaussianDom x := by
  have hle : -L ≤ L := by linarith
  rw [intervalIntegral.integral_of_le hle]
  exact setIntegral_le_integral involGaussianDom_integrable
    (Eventually.of_forall involGaussianDom_nonneg)

theorem invol_local_second_L1 :
    Tendsto
      (fun r : ℝ =>
        (∫ x in -(involSaddleDeltaReal r * Real.sqrt (involSaddleBReal r))..
          (involSaddleDeltaReal r * Real.sqrt (involSaddleBReal r)),
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleLocalRatio involFun involSaddleAReal involSaddleBReal r
                (x / Real.sqrt (involSaddleBReal r)) -
              saddleSecondPoly involSaddleBReal involSaddleB3Real involSaddleB4Real r x)‖) /
          involSecondCorrScale r)
      atTop (𝓝 0) := by
  let M : ℝ := ∫ x : ℝ, involGaussianDom x
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact involGaussianDom_integral_nonneg
  have hupper_tendsto :
      Tendsto (fun r : ℝ => (involLocalL1Const * M * (27 / 16 : ℝ)) / r)
        atTop (𝓝 0) := by
    have hinv : Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero
    simpa [div_eq_mul_inv, mul_assoc] using
      hinv.const_mul (involLocalL1Const * M * (27 / 16 : ℝ))
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
            (saddleLocalRatio involFun involSaddleAReal involSaddleBReal r
                (x / Real.sqrt (involSaddleBReal r)) -
              saddleSecondPoly involSaddleBReal involSaddleB3Real involSaddleB4Real r x)‖ :=
      intervalIntegral.integral_nonneg hle (fun _ _ => norm_nonneg _)
    exact div_nonneg hint_nonneg hcorr.le
  · filter_upwards [eventually_ge_atTop (1 : ℝ), invol_delta_le_one_eventually,
      invol_local_exponent_norm_le_eventually,
      involLocalBound_tendsto_zero.eventually_le_const zero_lt_one,
      involSecondCorrScale_lower_eventually, involSecondCorrScale_pos_eventually] with
      r hr hδle hloc hsmall hcorrLower hcorrPos
    let L : ℝ := involSaddleDeltaReal r * Real.sqrt (involSaddleBReal r)
    let F : ℝ → ℝ := fun x =>
      ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleLocalRatio involFun involSaddleAReal involSaddleBReal r
            (x / Real.sqrt (involSaddleBReal r)) -
          saddleSecondPoly involSaddleBReal involSaddleB3Real involSaddleB4Real r x)‖
    let G : ℝ → ℝ := fun x => (involLocalL1Const / r ^ 3) * involGaussianDom x
    have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
    have hbpos : 0 < involSaddleBReal r := involSaddleBReal_pos_of_ge_one hr
    have hsqrt_pos : 0 < Real.sqrt (involSaddleBReal r) := Real.sqrt_pos.mpr hbpos
    have hδnonneg : 0 ≤ involSaddleDeltaReal r := by
      unfold involSaddleDeltaReal
      positivity
    have hLnonneg : 0 ≤ L := by
      dsimp [L]
      positivity
    have hle : -L ≤ L := by linarith
    have hpoint : ∀ x ∈ Set.Icc (-L) L, F x ≤ G x := by
      intro x hx
      have hxabs : |x| ≤ L := by
        exact abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
      have hθδ : |x / Real.sqrt (involSaddleBReal r)| ≤ involSaddleDeltaReal r := by
        rw [abs_div, abs_of_pos hsqrt_pos]
        calc
          |x| / Real.sqrt (involSaddleBReal r) ≤
              L / Real.sqrt (involSaddleBReal r) :=
            div_le_div_of_nonneg_right hxabs hsqrt_pos.le
          _ = involSaddleDeltaReal r := by
            dsimp [L]
            field_simp [hsqrt_pos.ne']
      have hθone : |x / Real.sqrt (involSaddleBReal r)| ≤ 1 := hθδ.trans hδle
      have hx2r : |x| ≤ 2 * r := by
        calc
          |x| ≤ L := hxabs
          _ ≤ Real.sqrt (involSaddleBReal r) := by
            dsimp [L]
            simpa [one_mul] using
              mul_le_mul_of_nonneg_right hδle (Real.sqrt_nonneg _)
          _ ≤ 2 * r := invol_sqrtB_le_two_r hr
      have hWnorm :
          ‖involLocalExponent r (x / Real.sqrt (involSaddleBReal r))‖ ≤ 1 :=
        (hloc (x / Real.sqrt (involSaddleBReal r)) hθδ).trans hsmall
      have hb := invol_local_integrand_bound hr hθone hx2r hWnorm
      dsimp [F, G]
      calc
        ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleLocalRatio involFun involSaddleAReal involSaddleBReal r
                (x / Real.sqrt (involSaddleBReal r)) -
              saddleSecondPoly involSaddleBReal involSaddleB3Real involSaddleB4Real r x)‖
            ≤ involLocalL1Const * involGaussianDom x / r ^ 3 := hb
        _ = involLocalL1Const / r ^ 3 * involGaussianDom x := by ring
    have hFint : IntervalIntegrable F volume (-L) L := by
      exact (invol_local_integrand_continuous r).intervalIntegrable _ _
    have hGint : IntervalIntegrable G volume (-L) L := by
      exact (involGaussianDom_continuous.const_mul (involLocalL1Const / r ^ 3)).intervalIntegrable _ _
    have hIntBound :
        (∫ x in -L..L, F x) ≤ (involLocalL1Const / r ^ 3) * M := by
      calc
        (∫ x in -L..L, F x) ≤ ∫ x in -L..L, G x :=
          intervalIntegral.integral_mono_on hle hFint hGint hpoint
        _ = (involLocalL1Const / r ^ 3) * (∫ x in -L..L, involGaussianDom x) := by
          dsimp [G]
          rw [intervalIntegral.integral_const_mul]
        _ ≤ (involLocalL1Const / r ^ 3) * M := by
          exact mul_le_mul_of_nonneg_left
            (by dsimp [M]; exact involGaussianDom_window_le_integral hLnonneg)
            (div_nonneg involLocalL1Const_pos.le (by positivity))
    have hnum_nonneg : 0 ≤ (involLocalL1Const / r ^ 3) * M :=
      mul_nonneg (div_nonneg involLocalL1Const_pos.le (by positivity)) hM_nonneg
    have hscale_pos : 0 < (16 / 27 : ℝ) * r ^ (-(2 : ℝ)) := by
      positivity
    have hmain :
        (∫ x in -L..L, F x) / involSecondCorrScale r ≤
          ((involLocalL1Const / r ^ 3) * M) /
            ((16 / 27 : ℝ) * r ^ (-(2 : ℝ))) := by
      calc
        (∫ x in -L..L, F x) / involSecondCorrScale r
            ≤ ((involLocalL1Const / r ^ 3) * M) / involSecondCorrScale r :=
              div_le_div_of_nonneg_right hIntBound hcorrPos.le
        _ ≤ ((involLocalL1Const / r ^ 3) * M) /
              ((16 / 27 : ℝ) * r ^ (-(2 : ℝ))) :=
            div_le_div_of_nonneg_left hnum_nonneg hscale_pos hcorrLower
    calc
      ((∫ x in -(involSaddleDeltaReal r * Real.sqrt (involSaddleBReal r))..
          (involSaddleDeltaReal r * Real.sqrt (involSaddleBReal r)),
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleLocalRatio involFun involSaddleAReal involSaddleBReal r
                (x / Real.sqrt (involSaddleBReal r)) -
              saddleSecondPoly involSaddleBReal involSaddleB3Real involSaddleB4Real r x)‖) /
          involSecondCorrScale r)
          = (∫ x in -L..L, F x) / involSecondCorrScale r := by rfl
      _ ≤ ((involLocalL1Const / r ^ 3) * M) /
            ((16 / 27 : ℝ) * r ^ (-(2 : ℝ))) := hmain
      _ = (involLocalL1Const * M * (27 / 16 : ℝ)) / r := by
        rw [Real.rpow_neg hrpos.le]
        field_simp [hrpos.ne']
        ring_nf
        norm_num

def involSecondOrderHAdmissibleCandidate : SecondOrderHAdmissible involHAdmissible where
  b3 := involSaddleB3Real
  b4 := involSaddleB4Real
  corrScale := involSecondCorrScale
  corrScale_pos := by
    simpa [involHAdmissible] using involSecondCorrScale_pos_eventually
  corrScale_tendsto_zero := by
    simpa [involHAdmissible] using involSecondCorrScale_tendsto_zero
  corrScale_dominates_correction := by
    refine ⟨1, by norm_num, ?_⟩
    exact Eventually.of_forall fun r => by
      simp [involHAdmissible, involSecondCorrScale]
  local_second_L1 := by
    simpa [involHAdmissible] using invol_local_second_L1
  tail_second_uniform := by
    simpa [involHAdmissible] using invol_tail_second_uniform

lemma involSecondCorrScale_saddleRadius_isBigO_one_over_n :
    (fun n : ℕ => (involSecondCorrScale (involSaddleRadius n) : ℂ))
      =O[atTop] involOneOverNScale := by
  refine IsBigO.of_bound (200 : ℝ) ?_
  have hle_seq : ∀ᶠ n : ℕ in atTop,
      involSecondCorrScale (involSaddleRadius n) ≤
        100 * (involSaddleRadius n) ^ (-(2 : ℝ)) :=
    involSaddleRadius_tendsto_atTop.eventually involSecondCorrScale_le_rpow_eventually
  have hnonneg_seq : ∀ᶠ n : ℕ in atTop,
      0 ≤ involSecondCorrScale (involSaddleRadius n) :=
    involSaddleRadius_tendsto_atTop.eventually involSecondCorrScale_nonneg_eventually
  have hr_ge_one : ∀ᶠ n : ℕ in atTop, 1 ≤ involSaddleRadius n :=
    involSaddleRadius_tendsto_atTop.eventually_ge_atTop 1
  filter_upwards [hle_seq, hnonneg_seq, hr_ge_one, eventually_gt_atTop (0 : ℕ)] with
    n hle hnonneg hr1 hnpos
  let r := involSaddleRadius n
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  have hnRpos : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hn_eq : (n : ℝ) = r + r ^ 2 := by
    change (n : ℝ) = involSaddleAReal r
    rw [involSaddleAReal_radius]
  have hn_le : (n : ℝ) ≤ 2 * r ^ 2 := by
    rw [hn_eq]
    nlinarith [hr1]
  have hinv : r ^ (-(2 : ℝ)) ≤ 2 * ((1 : ℝ) / (n : ℝ)) := by
    rw [Real.rpow_neg hrpos.le]
    field_simp [hrpos.ne', hnRpos.ne']
    have hr2_rpow : r ^ 2 = r ^ (2 : ℝ) := by
      exact (Real.rpow_natCast r 2).symm
    rw [← hr2_rpow]
    nlinarith [hn_le]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
  dsimp [involOneOverNScale]
  rw [norm_div, norm_one, Complex.norm_natCast]
  calc
    involSecondCorrScale (involSaddleRadius n) ≤ 100 * r ^ (-(2 : ℝ)) := by
      simpa [r] using hle
    _ ≤ 100 * (2 * ((1 : ℝ) / (n : ℝ))) :=
      mul_le_mul_of_nonneg_left hinv (by norm_num)
    _ = 200 * (1 / (n : ℝ)) := by ring

lemma invol_saddleCorrection_radius_diff_eq
    (n : ℕ) (_hnpos : 0 < n) (hr1 : 1 ≤ involSaddleRadius n) :
    (saddleCorrection involSaddleBReal involSaddleB3Real involSaddleB4Real
        (involSaddleRadius n) : ℂ) + (1 : ℂ) / (6 * (n : ℂ)) =
      (((3 * (involSaddleRadius n) ^ 2 + 6 * involSaddleRadius n + 1) /
        (12 * involSaddleRadius n * (1 + 2 * involSaddleRadius n) ^ 3 *
          (1 + involSaddleRadius n)) : ℝ) : ℂ) := by
  let r := involSaddleRadius n
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  have hn_eq : (n : ℝ) = r + r ^ 2 := by
    change (n : ℝ) = involSaddleAReal r
    rw [involSaddleAReal_radius]
  have hreal :
      saddleCorrection involSaddleBReal involSaddleB3Real involSaddleB4Real r +
        (1 : ℝ) / (6 * (n : ℝ)) =
        (3 * r ^ 2 + 6 * r + 1) /
          (12 * r * (1 + 2 * r) ^ 3 * (1 + r)) := by
    rw [invol_saddleCorrection_eq hrpos.ne']
    rw [hn_eq]
    have h1r : 1 + r ≠ 0 := by positivity
    have h12r : 1 + 2 * r ≠ 0 := by positivity
    field_simp [hrpos.ne', h1r, h12r]
    ring
  have hcomplex :
      (1 : ℂ) / (6 * (n : ℂ)) = (((1 : ℝ) / (6 * (n : ℝ))) : ℂ) := by
    norm_num
  change (saddleCorrection involSaddleBReal involSaddleB3Real involSaddleB4Real r : ℂ) +
      (1 : ℂ) / (6 * (n : ℂ)) = _
  rw [hcomplex]
  exact_mod_cast hreal

lemma invol_saddleCorrection_radius_isLittleO_one_over_n :
    (fun n : ℕ =>
      (saddleCorrection involSaddleBReal involSaddleB3Real involSaddleB4Real
        (involSaddleRadius n) : ℂ) + (1 : ℂ) / (6 * (n : ℂ)))
      =o[atTop] involOneOverNScale := by
  let u : ℕ → ℂ := fun n =>
    (saddleCorrection involSaddleBReal involSaddleB3Real involSaddleB4Real
      (involSaddleRadius n) : ℂ) + (1 : ℂ) / (6 * (n : ℂ))
  let c : ℕ → ℝ := fun n => (1 : ℝ) / (n : ℝ)
  have hcpos : ∀ᶠ n in atTop, 0 < c n := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnRpos : 0 < (n : ℝ) := by exact_mod_cast hn
    exact div_pos zero_lt_one hnRpos
  have hdiv : Tendsto (fun n : ℕ => ‖u n‖ / c n) atTop (𝓝 0) := by
    have hrtop : Tendsto (fun n : ℕ => (involSaddleRadius n)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp involSaddleRadius_tendsto_atTop
    refine squeeze_zero' ?_ ?_ hrtop
    · filter_upwards [hcpos] with n hcn
      exact div_nonneg (norm_nonneg _) hcn.le
    · have hr_ge_one : ∀ᶠ n : ℕ in atTop, 1 ≤ involSaddleRadius n :=
        involSaddleRadius_tendsto_atTop.eventually_ge_atTop 1
      filter_upwards [eventually_gt_atTop (0 : ℕ), hr_ge_one] with n hnpos hr1
      let r := involSaddleRadius n
      have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr1
      have hn_eq : (n : ℝ) = r + r ^ 2 := by
        change (n : ℝ) = involSaddleAReal r
        rw [involSaddleAReal_radius]
      have hdiff := invol_saddleCorrection_radius_diff_eq n hnpos hr1
      have hreal_nonneg :
          0 ≤ (3 * r ^ 2 + 6 * r + 1) /
            (12 * r * (1 + 2 * r) ^ 3 * (1 + r)) := by positivity
      have hnorm : ‖u n‖ =
          (3 * r ^ 2 + 6 * r + 1) /
            (12 * r * (1 + 2 * r) ^ 3 * (1 + r)) := by
        change ‖(saddleCorrection involSaddleBReal involSaddleB3Real involSaddleB4Real
          (involSaddleRadius n) : ℂ) + (1 : ℂ) / (6 * (n : ℂ))‖ = _
        rw [hdiff]
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hreal_nonneg]
      rw [hnorm]
      have hratio : ((3 * r ^ 2 + 6 * r + 1) /
          (12 * r * (1 + 2 * r) ^ 3 * (1 + r))) / c n =
          (3 * r ^ 2 + 6 * r + 1) / (12 * (1 + 2 * r) ^ 3) := by
        dsimp [c]
        rw [hn_eq]
        have h1r : 1 + r ≠ 0 := by positivity
        have h12r : 1 + 2 * r ≠ 0 := by positivity
        field_simp [hrpos.ne', h1r, h12r]
      rw [hratio]
      have hnum : 3 * r ^ 2 + 6 * r + 1 ≤ 10 * r ^ 2 := by nlinarith [hr1]
      calc
        (3 * r ^ 2 + 6 * r + 1) / (12 * (1 + 2 * r) ^ 3)
            ≤ (10 * r ^ 2) / (12 * (1 + 2 * r) ^ 3) := by
              exact div_le_div_of_nonneg_right hnum (by positivity)
        _ ≤ r⁻¹ := by
          field_simp [hrpos.ne']
          ring_nf
          nlinarith [hr1, show 0 ≤ r ^ 2 by positivity, show 0 ≤ r ^ 3 by positivity]
  have hmain := complex_isLittleO_of_norm_div_tendsto_zero_nat u c hcpos hdiv
  refine (hmain.congr_left ?_).congr_right ?_
  · intro n
    simp [u]
  · intro n
    simp [c, involOneOverNScale]

/--
The single remaining analytical gap for this add-on: the second-order Hayman
verification for involutions (local L1 expansion through order six, tail bound
on the correction scale, and the final reduction of the signed correction to
`-1/(6n)`).  Once this estimate is supplied, the wrapper and final theorem below
are pure projections.
-/
theorem invol_secondOrder_gap :
    ∃ h2 : SecondOrderHAdmissible involHAdmissible,
      h2.b3 = involSaddleB3Real ∧
      h2.b4 = involSaddleB4Real ∧
      h2.corrScale = involSecondCorrScale ∧
      (fun n : ℕ => involSecondOrderOneOverNError n)
        =o[atTop] involOneOverNScale := by
  let h2 := involSecondOrderHAdmissibleCandidate
  have hcoeff_raw :=
    coeff_secondOrder_saddle involHAdmissible h2 involHAdmissibleSaddleSequence
  have hcoeff_corr :
      (fun n : ℕ =>
        involSeries.coeff n / involSecondOrderSaddleScale n -
          (1 + (saddleCorrection involSaddleBReal involSaddleB3Real involSaddleB4Real
            (involSaddleRadius n) : ℂ)))
        =o[atTop]
      (fun n : ℕ => (involSecondCorrScale (involSaddleRadius n) : ℂ)) := by
    simpa [h2, involSecondOrderSaddleScale, HAdmissible.B, involHAdmissible,
      involHAdmissibleSaddleSequence, involSecondOrderHAdmissibleCandidate,
      involSecondCorrScale] using hcoeff_raw
  have hcoeff_one_over_n :
      (fun n : ℕ =>
        involSeries.coeff n / involSecondOrderSaddleScale n -
          (1 + (saddleCorrection involSaddleBReal involSaddleB3Real involSaddleB4Real
            (involSaddleRadius n) : ℂ)))
        =o[atTop] involOneOverNScale :=
    hcoeff_corr.trans_isBigO involSecondCorrScale_saddleRadius_isBigO_one_over_n
  have hcorr := invol_saddleCorrection_radius_isLittleO_one_over_n
  have hsum := hcoeff_one_over_n.add hcorr
  refine ⟨h2, rfl, rfl, rfl, ?_⟩
  refine hsum.congr_left ?_
  intro n
  simp [involSecondOrderOneOverNError, involCoeffC, involSecondOrderSaddleScale,
    involSeries, PowerSeries.coeff_toFMLS, involCarrier_coeff, involCoeffR]
  ring

/-- The produced second-order H-admissible involution instance. -/
def involSecondOrderHAdmissible : SecondOrderHAdmissible involHAdmissible :=
  Classical.choose invol_secondOrder_gap

lemma involSecondOrderHAdmissible_b3 :
    involSecondOrderHAdmissible.b3 = involSaddleB3Real :=
  (Classical.choose_spec invol_secondOrder_gap).1

lemma involSecondOrderHAdmissible_b4 :
    involSecondOrderHAdmissible.b4 = involSaddleB4Real :=
  (Classical.choose_spec invol_secondOrder_gap).2.1

lemma involSecondOrderHAdmissible_corrScale :
    involSecondOrderHAdmissible.corrScale = involSecondCorrScale :=
  (Classical.choose_spec invol_secondOrder_gap).2.2.1

/-- Abstract second-order saddle theorem specialized to the involution saddle. -/
theorem invol_coeff_secondOrder_saddle_from_HAdmissible :
    (fun n : ℕ =>
      involSeries.coeff n / involSecondOrderSaddleScale n -
        (1 + (saddleCorrection involSaddleBReal involSaddleB3Real involSaddleB4Real
          (involSaddleRadius n) : ℂ)))
      =o[atTop]
    (fun n : ℕ => (involSecondCorrScale (involSaddleRadius n) : ℂ)) := by
  have h :=
    coeff_secondOrder_saddle
      involHAdmissible involSecondOrderHAdmissible involHAdmissibleSaddleSequence
  simpa [involSecondOrderSaddleScale, HAdmissible.B, involHAdmissible,
    involHAdmissibleSaddleSequence, involSecondOrderHAdmissible_b3,
    involSecondOrderHAdmissible_b4, involSecondOrderHAdmissible_corrScale,
    involSecondCorrScale] using h

/--
Second-order Moser-Wyman saddle ratio for involutions:
`[z^n] exp(z+z^2/2) = saddleScale_n * (1 - 1/(6n) + o(1/n))`.
-/
theorem involution_count_over_factorial_secondOrder_one_over_n :
    (fun n : ℕ => involSecondOrderOneOverNError n)
      =o[atTop] involOneOverNScale :=
  (Classical.choose_spec invol_secondOrder_gap).2.2.2

end InvolutionHAdmissible
