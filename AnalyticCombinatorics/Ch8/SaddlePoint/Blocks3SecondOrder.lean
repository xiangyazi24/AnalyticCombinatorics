import AnalyticCombinatorics.Ch8.SaddlePoint.SecondOrderHAdmissible
import AnalyticCombinatorics.Ch8.SaddlePoint.Blocks3HAdmissible

/-!
# Second-order saddle data for blocks of size at most three

This file adds the second-order correction layer for
`exp (z + z^2 / 2 + z^3 / 6)`.  The logarithmic saddle derivatives are
`b₃(r)=r+4r²+9r³/2` and `b₄(r)=r+8r²+27r³/2`.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval PowerSeries

set_option maxHeartbeats 800000

noncomputable section

namespace Blocks3HAdmissible

/-- Third logarithmic saddle derivative for blocks of size at most three. -/
def blocks3SaddleB3Real (r : ℝ) : ℝ :=
  r + 4 * r ^ 2 + 9 * r ^ 3 / 2

/-- Fourth logarithmic saddle derivative for blocks of size at most three. -/
def blocks3SaddleB4Real (r : ℝ) : ℝ :=
  r + 8 * r ^ 2 + 27 * r ^ 3 / 2

/-- A robust second-order comparison scale for the cubic saddle. -/
def blocks3SecondCorrScale (r : ℝ) : ℝ :=
  r ^ (-(3 : ℝ))

/-- Complex saddle scale used by the blocks-≤3 second-order statement. -/
def blocks3SecondOrderSaddleScale (n : ℕ) : ℂ :=
  saddleScale blocks3Fun blocks3SaddleRadius
    (fun n => blocks3SaddleBReal (blocks3SaddleRadius n)) n

/-- The explicit second-order correction at the saddle radius. -/
def blocks3SecondCorrectionAtSaddle (n : ℕ) : ℝ :=
  saddleCorrection blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real
    (blocks3SaddleRadius n)

/-- Error term for the formal blocks-≤3 EGF coefficient. -/
def blocks3SecondOrderSeriesError (n : ℕ) : ℂ :=
  blocks3Series.coeff n / blocks3SecondOrderSaddleScale n -
    (1 + (blocks3SecondCorrectionAtSaddle n : ℂ))

/-- Error term for `B₃(n) / n!`. -/
def blocks3SecondOrderNumberError (n : ℕ) : ℂ :=
  (((AnalyticCombinatorics.Ch1.CombClass.blocks3.counts n : ℝ) /
      n.factorial : ℝ) : ℂ) /
    blocks3SecondOrderSaddleScale n -
      (1 + (blocks3SecondCorrectionAtSaddle n : ℂ))

lemma blocks3SecondCorrScale_pos_eventually :
    ∀ᶠ r : ℝ in atTop, 0 < blocks3SecondCorrScale r := by
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  unfold blocks3SecondCorrScale
  exact Real.rpow_pos_of_pos hr _

lemma blocks3SecondCorrScale_tendsto_zero :
    Tendsto blocks3SecondCorrScale atTop (𝓝 0) := by
  change Tendsto (fun r : ℝ => r ^ (-(3 : ℝ))) atTop (𝓝 0)
  exact tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3)

lemma blocks3_saddleCorrectionScale_le_secondCorrScale_eventually :
    ∀ᶠ r : ℝ in atTop,
      saddleCorrectionScale blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real r ≤
        1000000 * blocks3SecondCorrScale r := by
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hbpos : 0 < blocks3SaddleBReal r := by
    unfold blocks3SaddleBReal
    positivity
  have hb4_nonneg : 0 ≤ blocks3SaddleB4Real r := by
    unfold blocks3SaddleB4Real
    positivity
  unfold saddleCorrectionScale blocks3SaddleBReal blocks3SaddleB3Real
    blocks3SaddleB4Real blocks3SecondCorrScale
  rw [abs_of_nonneg (by simpa [blocks3SaddleB4Real] using hb4_nonneg)]
  rw [Real.rpow_neg hrpos.le]
  field_simp [hrpos.ne', hbpos.ne']
  ring_nf
  have h1_le_r2 : (1 : ℝ) ≤ r ^ 2 := by
    nlinarith [sq_nonneg (r - 1)]
  have h1_le_r3 : (1 : ℝ) ≤ r ^ 3 := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ r * r ^ 2 :=
        mul_le_mul hr h1_le_r2 zero_le_one (le_trans zero_le_one hr)
      _ = r ^ 3 := by ring
  have h1_le_r4 : (1 : ℝ) ≤ r ^ 4 := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ r ^ 2 * r ^ 2 :=
        mul_le_mul h1_le_r2 h1_le_r2 zero_le_one (sq_nonneg r)
      _ = r ^ 4 := by ring
  have hr3_le_r7 : r ^ 3 ≤ r ^ 7 := by
    calc
      r ^ 3 = r ^ 3 * 1 := by ring
      _ ≤ r ^ 3 * r ^ 4 :=
        mul_le_mul_of_nonneg_left h1_le_r4 (by positivity)
      _ = r ^ 7 := by ring
  have hr4_le_r7 : r ^ 4 ≤ r ^ 7 := by
    calc
      r ^ 4 = r ^ 4 * 1 := by ring
      _ ≤ r ^ 4 * r ^ 3 :=
        mul_le_mul_of_nonneg_left h1_le_r3 (by positivity)
      _ = r ^ 7 := by ring
  have hr5_le_r7 : r ^ 5 ≤ r ^ 7 := by
    calc
      r ^ 5 = r ^ 5 * 1 := by ring
      _ ≤ r ^ 5 * r ^ 2 :=
        mul_le_mul_of_nonneg_left h1_le_r2 (by positivity)
      _ = r ^ 7 := by ring
  have hr6_le_r7 : r ^ 6 ≤ r ^ 7 := by
    calc
      r ^ 6 = r ^ 6 * 1 := by ring
      _ ≤ r ^ 6 * r := mul_le_mul_of_nonneg_left hr (by positivity)
      _ = r ^ 7 := by ring
  calc
    r * r ^ (3 : ℝ) * 144 + r ^ 2 * r ^ (3 : ℝ) * 448 +
          r ^ 3 * r ^ (3 : ℝ) * 600 + r ^ 4 * r ^ (3 : ℝ) * 324 +
            r ^ (3 : ℝ) * 16
        = 144 * r ^ 4 + 448 * r ^ 5 + 600 * r ^ 6 + 324 * r ^ 7 +
            16 * r ^ 3 := by
          rw [show r ^ (3 : ℝ) = r ^ 3 by
            exact Real.rpow_natCast r 3]
          ring
    _ ≤ 144 * r ^ 7 + 448 * r ^ 7 + 600 * r ^ 7 + 324 * r ^ 7 +
          16 * r ^ 7 := by
        gcongr
    _ ≤ r * 8000000 + r ^ 2 * 48000000 + r ^ 3 * 132000000 +
          r ^ 4 * 208000000 + r ^ 5 * 198000000 + r ^ 6 * 108000000 +
            r ^ 7 * 27000000 := by
        nlinarith [show 0 ≤ r by positivity, show 0 ≤ r ^ 2 by positivity,
          show 0 ≤ r ^ 3 by positivity, show 0 ≤ r ^ 4 by positivity,
          show 0 ≤ r ^ 5 by positivity, show 0 ≤ r ^ 6 by positivity,
          show 0 ≤ r ^ 7 by positivity]

lemma blocks3_tail_second_decay :
    Tendsto
      (fun r : ℝ =>
        Real.sqrt (2 * Real.pi * blocks3SaddleBReal r) * blocks3TailE r /
          blocks3SecondCorrScale r)
      atTop (𝓝 0) := by
  let c : ℝ := 1 / (2 * Real.pi ^ 2)
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hbase :
      Tendsto (fun y : ℝ => y ^ (27 / 4 : ℝ) * Real.exp (-c * y)) atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (27 / 4 : ℝ) c hc
  have hy : Tendsto (fun r : ℝ => r ^ (2 / 3 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)
  have hcomp :
      Tendsto (fun r : ℝ => (r ^ (2 / 3 : ℝ)) ^ (27 / 4 : ℝ) *
        Real.exp (-c * r ^ (2 / 3 : ℝ))) atTop (𝓝 0) :=
    hbase.comp hy
  have hscaled :
      Tendsto (fun r : ℝ => Real.sqrt (10 * Real.pi) *
        ((r ^ (2 / 3 : ℝ)) ^ (27 / 4 : ℝ) *
          Real.exp (-c * r ^ (2 / 3 : ℝ)))) atTop (𝓝 0) := by
    simpa using hcomp.const_mul (Real.sqrt (10 * Real.pi))
  refine squeeze_zero' ?_ ?_ hscaled
  · filter_upwards [blocks3SecondCorrScale_pos_eventually] with r hcorr
    exact div_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) (by unfold blocks3TailE; positivity)) hcorr.le
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    have hr0 : 0 ≤ r := le_trans zero_le_one hr
    have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
    have hcorr_pos : 0 < blocks3SecondCorrScale r := by
      unfold blocks3SecondCorrScale
      exact Real.rpow_pos_of_pos hrpos _
    have one_le_r2 : 1 ≤ r ^ 2 := by nlinarith [hr, sq_nonneg (r - 1)]
    have hr_le_r3 : r ≤ r ^ 3 := by
      calc
        r = r * 1 := by ring
        _ ≤ r * r ^ 2 := mul_le_mul_of_nonneg_left one_le_r2 hr0
        _ = r ^ 3 := by ring
    have hr2_le_r3 : r ^ 2 ≤ r ^ 3 := by
      calc
        r ^ 2 = r ^ 2 * 1 := by ring
        _ ≤ r ^ 2 * r := mul_le_mul_of_nonneg_left hr (sq_nonneg r)
        _ = r ^ 3 := by ring
    have hB_le : blocks3SaddleBReal r ≤ 5 * r ^ 3 := by
      unfold blocks3SaddleBReal
      nlinarith
    have hsqrt :
        Real.sqrt (2 * Real.pi * blocks3SaddleBReal r) ≤
          Real.sqrt (10 * Real.pi) * r ^ (3 / 2 : ℝ) := by
      have hmul : 2 * Real.pi * blocks3SaddleBReal r ≤ 10 * Real.pi * r ^ 3 := by
        calc
          2 * Real.pi * blocks3SaddleBReal r
              ≤ 2 * Real.pi * (5 * r ^ 3) :=
                mul_le_mul_of_nonneg_left hB_le (by positivity)
          _ = 10 * Real.pi * r ^ 3 := by ring_nf
      calc
        Real.sqrt (2 * Real.pi * blocks3SaddleBReal r)
            ≤ Real.sqrt (10 * Real.pi * r ^ 3) := Real.sqrt_le_sqrt hmul
        _ = Real.sqrt (10 * Real.pi) * r ^ (3 / 2 : ℝ) := by
          have h10pi : 0 ≤ 10 * Real.pi := by positivity
          rw [Real.sqrt_mul h10pi (r ^ 3)]
          rw [Real.sqrt_eq_rpow (r ^ 3)]
          have hpow : (r ^ 3) ^ (1 / 2 : ℝ) = r ^ (3 / 2 : ℝ) := by
            rw [← Real.rpow_natCast]
            rw [← Real.rpow_mul hr0]
            norm_num
          rw [hpow]
    have hE_nonneg : 0 ≤ blocks3TailE r := by
      unfold blocks3TailE
      positivity
    have hnum :
        Real.sqrt (2 * Real.pi * blocks3SaddleBReal r) * blocks3TailE r ≤
          (Real.sqrt (10 * Real.pi) * r ^ (3 / 2 : ℝ)) * blocks3TailE r :=
      mul_le_mul_of_nonneg_right hsqrt hE_nonneg
    have hrpow :
        (r ^ (2 / 3 : ℝ)) ^ (27 / 4 : ℝ) = r ^ (9 / 2 : ℝ) := by
      rw [← Real.rpow_mul hr0]
      norm_num
    calc
      Real.sqrt (2 * Real.pi * blocks3SaddleBReal r) * blocks3TailE r /
          blocks3SecondCorrScale r
          ≤ (Real.sqrt (10 * Real.pi) * r ^ (3 / 2 : ℝ)) * blocks3TailE r /
              blocks3SecondCorrScale r :=
            div_le_div_of_nonneg_right hnum hcorr_pos.le
      _ = Real.sqrt (10 * Real.pi) *
            ((r ^ (2 / 3 : ℝ)) ^ (27 / 4 : ℝ) *
              Real.exp (-c * r ^ (2 / 3 : ℝ))) := by
        unfold blocks3TailE blocks3SecondCorrScale
        dsimp [c]
        rw [Real.rpow_neg hr0]
        rw [hrpow]
        field_simp [hrpos.ne']
        rw [← Real.rpow_add hrpos]
        norm_num

lemma blocks3_tail_second_uniform :
    ∃ E : ℝ → ℝ,
      (∀ᶠ r : ℝ in atTop, 0 ≤ E r) ∧
      Tendsto
        (fun r : ℝ => Real.sqrt (2 * Real.pi * blocks3SaddleBReal r) * E r /
          blocks3SecondCorrScale r)
        atTop (𝓝 0) ∧
      (∀ᶠ r : ℝ in atTop, ∀ n : ℕ, ∀ θ : ℝ,
        blocks3SaddleDeltaReal r ≤ |θ| → |θ| ≤ Real.pi →
          ‖saddleGAt blocks3Fun r n θ‖ ≤ E r) := by
  exact ⟨blocks3TailE, blocks3TailE_nonneg_eventually, blocks3_tail_second_decay,
    blocks3_tail_bound_eventually⟩

private def expLocalRemainderFifth (θ : ℝ) : ℂ :=
  ExpStirling.expLocalRemainder θ -
    ((((θ : ℂ) * Complex.I) ^ 3) / (((3 : ℕ).factorial : ℕ) : ℂ) +
      (((θ : ℂ) * Complex.I) ^ 4) / (((4 : ℕ).factorial : ℕ) : ℂ))

private lemma expLocalRemainderFifth_norm_le {θ : ℝ} (hθ : |θ| ≤ 3) :
    ‖expLocalRemainderFifth θ‖ ≤ Real.exp 3 * |θ| ^ 5 := by
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
      Real.exp 3 * |θ| ^ 5
  rw [hleft]
  calc
    ‖Complex.exp u - ∑ m ∈ Finset.range 5, u ^ m / (m.factorial : ℂ)‖
        ≤ ‖u‖ ^ 5 * Real.exp ‖u‖ := htail
    _ = |θ| ^ 5 * Real.exp |θ| := by rw [hnorm]
    _ ≤ |θ| ^ 5 * Real.exp 3 := by
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hθ)
        (pow_nonneg (abs_nonneg θ) 5)
    _ = Real.exp 3 * |θ| ^ 5 := by ring

private lemma blocks3LocalExponent_split_fifth (r θ : ℝ) :
    blocks3LocalExponent r θ =
      -Complex.I * ((blocks3SaddleB3Real r : ℂ) / 6) * (θ : ℂ) ^ 3 +
        ((blocks3SaddleB4Real r : ℂ) / 24) * (θ : ℂ) ^ 4 +
        (r : ℂ) * expLocalRemainderFifth θ +
        (((r ^ 2 / 2 : ℝ) : ℂ) * expLocalRemainderFifth (2 * θ)) +
          (((r ^ 3 / 6 : ℝ) : ℂ) * expLocalRemainderFifth (3 * θ)) := by
  unfold blocks3LocalExponent expLocalRemainderFifth blocks3SaddleB3Real blocks3SaddleB4Real
  ring_nf
  simp [Complex.I_pow_three, Complex.I_pow_four]
  ring_nf

private def blocks3ScaledCubic (r x : ℝ) : ℂ :=
  -Complex.I *
    ((blocks3SaddleB3Real r : ℂ) /
      (6 * (Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 3)) * (x : ℂ) ^ 3

private def blocks3ScaledQuartic (r x : ℝ) : ℂ :=
  ((blocks3SaddleB4Real r : ℂ) /
      (24 * (Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 4)) *
    (x : ℂ) ^ 4

private def blocks3ScaledRemainder (r x : ℝ) : ℂ :=
  (r : ℂ) * expLocalRemainderFifth (x / Real.sqrt (blocks3SaddleBReal r)) +
    (((r ^ 2 / 2 : ℝ) : ℂ) *
      expLocalRemainderFifth (2 * (x / Real.sqrt (blocks3SaddleBReal r)))) +
      (((r ^ 3 / 6 : ℝ) : ℂ) *
        expLocalRemainderFifth (3 * (x / Real.sqrt (blocks3SaddleBReal r))))

private lemma blocks3SaddleBReal_pos_of_ge_one {r : ℝ} (hr : 1 ≤ r) :
    0 < blocks3SaddleBReal r := by
  unfold blocks3SaddleBReal
  positivity

private lemma blocks3_sqrtB_sq {r : ℝ} (hb : 0 < blocks3SaddleBReal r) :
    ((Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 2) =
      (blocks3SaddleBReal r : ℂ) := by
  exact_mod_cast (Real.sq_sqrt hb.le)

private lemma blocks3_sqrtB_ge_rpow_three_halves {r : ℝ} (hr : 1 ≤ r) :
    r ^ (3 / 2 : ℝ) ≤ Real.sqrt (blocks3SaddleBReal r) := by
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  have hb_ge : r ^ 3 ≤ blocks3SaddleBReal r := by
    unfold blocks3SaddleBReal
    nlinarith [sq_nonneg r, mul_nonneg (sq_nonneg r) hr0]
  have hrpow_sq : (r ^ (3 / 2 : ℝ)) ^ 2 = r ^ 3 := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hr0]
    norm_num
  exact Real.le_sqrt_of_sq_le (by simpa [hrpow_sq] using hb_ge)

private lemma blocks3LocalExponent_scaled_split {r x : ℝ}
    (hb : 0 < blocks3SaddleBReal r) :
    blocks3LocalExponent r (x / Real.sqrt (blocks3SaddleBReal r)) =
      blocks3ScaledCubic r x + blocks3ScaledQuartic r x + blocks3ScaledRemainder r x := by
  have hsqrt_ne : (Real.sqrt (blocks3SaddleBReal r) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hb).ne'
  have hsqrt_sq := blocks3_sqrtB_sq hb
  rw [blocks3LocalExponent_split_fifth]
  unfold blocks3ScaledCubic blocks3ScaledQuartic blocks3ScaledRemainder
  simp [Complex.ofReal_inv, div_eq_mul_inv]
  field_simp [hsqrt_ne]
  ring_nf

private lemma blocks3_saddleSecondPoly_eq_scaled_terms {r x : ℝ}
    (hb : 0 < blocks3SaddleBReal r) :
    saddleSecondPoly blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real r x =
      1 + blocks3ScaledCubic r x + blocks3ScaledQuartic r x +
        (blocks3ScaledCubic r x) ^ 2 / 2 := by
  have hsqrt_sq := blocks3_sqrtB_sq hb
  have hsqrt_ne : (Real.sqrt (blocks3SaddleBReal r) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hb).ne'
  have hb_ne : (blocks3SaddleBReal r : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hb.ne'
  have hsqrt_pow6 :
      (Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 6 =
        (blocks3SaddleBReal r : ℂ) ^ 3 := by
    calc
      (Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 6 =
          ((Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 2) ^ 3 := by ring
      _ = (blocks3SaddleBReal r : ℂ) ^ 3 := by rw [hsqrt_sq]
  have hsqrt_pow4 :
      (Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 4 =
        (blocks3SaddleBReal r : ℂ) ^ 2 := by
    calc
      (Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 4 =
          ((Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 2) ^ 2 := by ring
      _ = (blocks3SaddleBReal r : ℂ) ^ 2 := by rw [hsqrt_sq]
  unfold saddleSecondPoly blocks3ScaledCubic blocks3ScaledQuartic
  field_simp [hsqrt_ne, hb_ne]
  ring_nf
  rw [hsqrt_pow6, hsqrt_sq, Complex.I_sq]
  norm_num [Complex.ofReal_pow]
  ring

private lemma blocks3ScaledCubic_norm_le {r x : ℝ} (hr : 1 ≤ r) :
    ‖blocks3ScaledCubic r x‖ ≤ 10 * r ^ (-(3 / 2 : ℝ)) * |x| ^ 3 := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hr0 : 0 ≤ r := hrpos.le
  have hbpos : 0 < blocks3SaddleBReal r := blocks3SaddleBReal_pos_of_ge_one hr
  have hsqrt_pos : 0 < Real.sqrt (blocks3SaddleBReal r) := Real.sqrt_pos.mpr hbpos
  have hsqrt_ge : r ^ (3 / 2 : ℝ) ≤ Real.sqrt (blocks3SaddleBReal r) :=
    blocks3_sqrtB_ge_rpow_three_halves hr
  have hsqrt3_ge :
      (r ^ (3 / 2 : ℝ)) ^ 3 ≤ (Real.sqrt (blocks3SaddleBReal r)) ^ 3 :=
    pow_le_pow_left₀ (by positivity : 0 ≤ r ^ (3 / 2 : ℝ)) hsqrt_ge 3
  have hb3_nonneg : 0 ≤ blocks3SaddleB3Real r := by
    unfold blocks3SaddleB3Real
    positivity
  have hb3_le : blocks3SaddleB3Real r ≤ 10 * r ^ 3 := by
    unfold blocks3SaddleB3Real
    nlinarith [hr, sq_nonneg r, show 0 ≤ r ^ 3 by positivity]
  have hrpow3 :
      (r ^ (3 / 2 : ℝ)) ^ 3 = r ^ ((3 / 2 : ℝ) * 3) :=
    (Real.rpow_mul_natCast hr0 (3 / 2 : ℝ) 3).symm
  have hcoef :
      ‖(blocks3SaddleB3Real r : ℂ) /
          (6 * (Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 3)‖ ≤
        10 * r ^ (-(3 / 2 : ℝ)) := by
    calc
      ‖(blocks3SaddleB3Real r : ℂ) /
          (6 * (Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 3)‖
          = blocks3SaddleB3Real r /
              (6 * (Real.sqrt (blocks3SaddleBReal r)) ^ 3) := by
            rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg hb3_nonneg]
            simp only [norm_mul, norm_ofNat, norm_pow, Complex.norm_real, Real.norm_eq_abs]
            rw [abs_of_pos hsqrt_pos]
      _ ≤ (10 * r ^ 3) / (6 * (r ^ (3 / 2 : ℝ)) ^ 3) := by
            exact div_le_div₀ (by positivity) hb3_le (by positivity)
              (by nlinarith [hsqrt3_ge])
      _ ≤ 10 * r ^ (-(3 / 2 : ℝ)) := by
            rw [hrpow3]
            rw [show (3 / 2 : ℝ) * 3 = 3 + 3 / 2 by norm_num]
            rw [Real.rpow_add hrpos]
            rw [Real.rpow_neg hr0]
            have ha : 0 < r ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hrpos _
            have hnat3 : r ^ 3 = r ^ (3 : ℝ) := by
              exact (Real.rpow_natCast r 3).symm
            rw [← hnat3]
            have hden : 0 < 6 * (r ^ 3 * r ^ (3 / 2 : ℝ)) := by positivity
            rw [div_le_iff₀ hden]
            field_simp [ha.ne']
            nlinarith [show 0 ≤ r ^ 3 by positivity]
  calc
    ‖blocks3ScaledCubic r x‖
        = ‖(blocks3SaddleB3Real r : ℂ) /
            (6 * (Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 3)‖ * |x| ^ 3 := by
          unfold blocks3ScaledCubic
          rw [norm_mul, norm_mul, norm_neg, norm_I, one_mul, norm_pow,
            Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (10 * r ^ (-(3 / 2 : ℝ))) * |x| ^ 3 :=
      mul_le_mul_of_nonneg_right hcoef (pow_nonneg (abs_nonneg x) 3)
    _ = 10 * r ^ (-(3 / 2 : ℝ)) * |x| ^ 3 := by ring

private lemma blocks3ScaledQuartic_norm_le {r x : ℝ} (hr : 1 ≤ r) :
    ‖blocks3ScaledQuartic r x‖ ≤ 10 * r ^ (-(3 : ℝ)) * |x| ^ 4 := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hr0 : 0 ≤ r := hrpos.le
  have hbpos : 0 < blocks3SaddleBReal r := blocks3SaddleBReal_pos_of_ge_one hr
  have hb_ge : r ^ 3 ≤ blocks3SaddleBReal r := by
    unfold blocks3SaddleBReal
    nlinarith [sq_nonneg r, mul_nonneg (sq_nonneg r) hr0]
  have hb_sq_ge : (r ^ 3) ^ 2 ≤ (blocks3SaddleBReal r) ^ 2 :=
    pow_le_pow_left₀ (by positivity : 0 ≤ r ^ 3) hb_ge 2
  have hb4_nonneg : 0 ≤ blocks3SaddleB4Real r := by
    unfold blocks3SaddleB4Real
    positivity
  have hb4_le : blocks3SaddleB4Real r ≤ 30 * r ^ 3 := by
    unfold blocks3SaddleB4Real
    nlinarith [hr, sq_nonneg r, show 0 ≤ r ^ 3 by positivity]
  have hcoef :
      ‖(blocks3SaddleB4Real r : ℂ) /
          (24 * (Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 4)‖ ≤
        10 * r ^ (-(3 : ℝ)) := by
    calc
      ‖(blocks3SaddleB4Real r : ℂ) /
          (24 * (Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 4)‖
          = blocks3SaddleB4Real r / (24 * (Real.sqrt (blocks3SaddleBReal r)) ^ 4) := by
            rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg hb4_nonneg]
            simp only [norm_mul, norm_ofNat, norm_pow, Complex.norm_real, Real.norm_eq_abs]
            rw [abs_of_pos (Real.sqrt_pos.mpr hbpos)]
      _ ≤ (30 * r ^ 3) / (24 * (r ^ (3 / 2 : ℝ)) ^ 4) := by
            have hsqrt4_ge :
                (r ^ (3 / 2 : ℝ)) ^ 4 ≤ (Real.sqrt (blocks3SaddleBReal r)) ^ 4 :=
              pow_le_pow_left₀ (by positivity : 0 ≤ r ^ (3 / 2 : ℝ))
                (blocks3_sqrtB_ge_rpow_three_halves hr) 4
            exact div_le_div₀ (by positivity) hb4_le (by positivity)
              (by nlinarith [hsqrt4_ge])
      _ ≤ 10 * r ^ (-(3 : ℝ)) := by
            have hrpow4 :
                (r ^ (3 / 2 : ℝ)) ^ 4 = r ^ ((3 / 2 : ℝ) * 4) :=
              (Real.rpow_mul_natCast hr0 (3 / 2 : ℝ) 4).symm
            rw [hrpow4]
            rw [show (3 / 2 : ℝ) * 4 = 6 by norm_num]
            have hneg3 : r ^ (-(3 : ℝ)) = (r ^ 3)⁻¹ := by
              calc
                r ^ (-(3 : ℝ)) = (r ^ (3 : ℝ))⁻¹ := Real.rpow_neg hr0 (3 : ℝ)
                _ = (r ^ 3)⁻¹ := congrArg (fun t : ℝ => t⁻¹) (Real.rpow_natCast r 3)
            rw [hneg3]
            rw [show r ^ (6 : ℝ) = r ^ 6 by exact Real.rpow_natCast r 6]
            have hden : 0 < 24 * r ^ 6 := by positivity
            rw [div_le_iff₀ hden]
            field_simp [hrpos.ne']
            nlinarith [show 0 ≤ r ^ 3 by positivity, show 0 ≤ r ^ 6 by positivity]
  calc
    ‖blocks3ScaledQuartic r x‖
        = ‖(blocks3SaddleB4Real r : ℂ) /
            (24 * (Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 4)‖ * |x| ^ 4 := by
          unfold blocks3ScaledQuartic
          rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (10 * r ^ (-(3 : ℝ))) * |x| ^ 4 :=
      mul_le_mul_of_nonneg_right hcoef (pow_nonneg (abs_nonneg x) 4)
    _ = 10 * r ^ (-(3 : ℝ)) * |x| ^ 4 := by ring

private def blocks3LocalTaylorConst : ℝ :=
  10000 * Real.exp 3

private lemma blocks3LocalTaylorConst_pos : 0 < blocks3LocalTaylorConst := by
  unfold blocks3LocalTaylorConst
  positivity

private lemma blocks3ScaledRemainder_norm_le {r x : ℝ}
    (hr : 1 ≤ r) (hθ : |x / Real.sqrt (blocks3SaddleBReal r)| ≤ 1) :
    ‖blocks3ScaledRemainder r x‖ ≤
      blocks3LocalTaylorConst * r ^ (-(9 / 2 : ℝ)) * |x| ^ 5 := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hr0 : 0 ≤ r := hrpos.le
  have hbpos : 0 < blocks3SaddleBReal r := blocks3SaddleBReal_pos_of_ge_one hr
  have hsqrt_pos : 0 < Real.sqrt (blocks3SaddleBReal r) := Real.sqrt_pos.mpr hbpos
  have hsqrt_ge : r ^ (3 / 2 : ℝ) ≤ Real.sqrt (blocks3SaddleBReal r) :=
    blocks3_sqrtB_ge_rpow_three_halves hr
  let A : ℝ := r ^ (-(3 / 2 : ℝ))
  let D : ℝ := r ^ (-(9 / 2 : ℝ))
  let y : ℝ := |x|
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  have hD_nonneg : 0 ≤ D := by
    dsimp [D]
    positivity
  have hy0 : 0 ≤ y := by
    dsimp [y]
    exact abs_nonneg x
  have hA5D : r ^ 3 * A ^ 5 = D := by
    dsimp [A, D]
    rw [(Real.rpow_mul_natCast hr0 (-(3 / 2 : ℝ)) 5).symm]
    rw [show r ^ 3 = r ^ (3 : ℝ) by exact (Real.rpow_natCast r 3).symm]
    rw [← Real.rpow_add hrpos]
    norm_num
  have hA5_nonneg : 0 ≤ A ^ 5 := pow_nonneg hA_nonneg 5
  have hr_le_r3 : r ≤ r ^ 3 := by
    have h1_le_r2 : (1 : ℝ) ≤ r ^ 2 := by nlinarith [hr, sq_nonneg (r - 1)]
    calc
      r = r * 1 := by ring
      _ ≤ r * r ^ 2 := mul_le_mul_of_nonneg_left h1_le_r2 hr0
      _ = r ^ 3 := by ring
  have hr2_le_r3 : r ^ 2 ≤ r ^ 3 := by
    calc
      r ^ 2 = r ^ 2 * 1 := by ring
      _ ≤ r ^ 2 * r := mul_le_mul_of_nonneg_left hr (sq_nonneg r)
      _ = r ^ 3 := by ring
  have hrA5_le_D : r * A ^ 5 ≤ D := by
    calc
      r * A ^ 5 ≤ r ^ 3 * A ^ 5 :=
        mul_le_mul_of_nonneg_right hr_le_r3 hA5_nonneg
      _ = D := hA5D
  have hr2A5_le_D : r ^ 2 * A ^ 5 ≤ D := by
    calc
      r ^ 2 * A ^ 5 ≤ r ^ 3 * A ^ 5 :=
        mul_le_mul_of_nonneg_right hr2_le_r3 hA5_nonneg
      _ = D := hA5D
  have hr3A5_le_D : r ^ 3 * A ^ 5 ≤ D := by rw [hA5D]
  have hθ_abs_le : |x / Real.sqrt (blocks3SaddleBReal r)| ≤ A * y := by
    rw [abs_div, abs_of_pos hsqrt_pos]
    have hbase :
        |x| / Real.sqrt (blocks3SaddleBReal r) ≤ |x| / r ^ (3 / 2 : ℝ) :=
      div_le_div_of_nonneg_left (abs_nonneg x)
        (Real.rpow_pos_of_pos hrpos (3 / 2 : ℝ)) hsqrt_ge
    calc
      |x| / Real.sqrt (blocks3SaddleBReal r) ≤ |x| / r ^ (3 / 2 : ℝ) := hbase
      _ = A * y := by
        dsimp [A, y]
        rw [Real.rpow_neg hr0]
        ring
  have hθ_three : |x / Real.sqrt (blocks3SaddleBReal r)| ≤ 3 := hθ.trans (by norm_num)
  have h2θ_three : |2 * (x / Real.sqrt (blocks3SaddleBReal r))| ≤ 3 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  have h3θ_three : |3 * (x / Real.sqrt (blocks3SaddleBReal r))| ≤ 3 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    nlinarith
  have hrem1 := expLocalRemainderFifth_norm_le hθ_three
  have hrem2 := expLocalRemainderFifth_norm_le h2θ_three
  have hrem3 := expLocalRemainderFifth_norm_le h3θ_three
  have hθ5_le : |x / Real.sqrt (blocks3SaddleBReal r)| ^ 5 ≤ (A * y) ^ 5 :=
    pow_le_pow_left₀ (abs_nonneg _) hθ_abs_le 5
  have h2θ5_le :
      |2 * (x / Real.sqrt (blocks3SaddleBReal r))| ^ 5 ≤ (2 * A * y) ^ 5 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    simpa [mul_assoc] using
      pow_le_pow_left₀ (by positivity : 0 ≤ 2 * |x / Real.sqrt (blocks3SaddleBReal r)|)
        (mul_le_mul_of_nonneg_left hθ_abs_le (by norm_num)) 5
  have h3θ5_le :
      |3 * (x / Real.sqrt (blocks3SaddleBReal r))| ^ 5 ≤ (3 * A * y) ^ 5 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    simpa [mul_assoc] using
      pow_le_pow_left₀ (by positivity : 0 ≤ 3 * |x / Real.sqrt (blocks3SaddleBReal r)|)
        (mul_le_mul_of_nonneg_left hθ_abs_le (by norm_num)) 5
  have hmain :
      ‖blocks3ScaledRemainder r x‖ ≤
        r * (Real.exp 3 * (A * y) ^ 5) +
          (r ^ 2 / 2) * (Real.exp 3 * (2 * A * y) ^ 5) +
            (r ^ 3 / 6) * (Real.exp 3 * (3 * A * y) ^ 5) := by
    unfold blocks3ScaledRemainder
    calc
      ‖(r : ℂ) * expLocalRemainderFifth (x / Real.sqrt (blocks3SaddleBReal r)) +
          (((r ^ 2 / 2 : ℝ) : ℂ) *
            expLocalRemainderFifth (2 * (x / Real.sqrt (blocks3SaddleBReal r)))) +
            (((r ^ 3 / 6 : ℝ) : ℂ) *
              expLocalRemainderFifth (3 * (x / Real.sqrt (blocks3SaddleBReal r))))‖
          ≤ ‖(r : ℂ) * expLocalRemainderFifth (x / Real.sqrt (blocks3SaddleBReal r))‖ +
              ‖(((r ^ 2 / 2 : ℝ) : ℂ) *
                expLocalRemainderFifth (2 * (x / Real.sqrt (blocks3SaddleBReal r))))‖ +
                ‖(((r ^ 3 / 6 : ℝ) : ℂ) *
                  expLocalRemainderFifth (3 * (x / Real.sqrt (blocks3SaddleBReal r))))‖ := by
            calc
              ‖(r : ℂ) * expLocalRemainderFifth (x / Real.sqrt (blocks3SaddleBReal r)) +
                  (((r ^ 2 / 2 : ℝ) : ℂ) *
                    expLocalRemainderFifth (2 * (x / Real.sqrt (blocks3SaddleBReal r)))) +
                    (((r ^ 3 / 6 : ℝ) : ℂ) *
                      expLocalRemainderFifth (3 * (x / Real.sqrt (blocks3SaddleBReal r))))‖
                  ≤ ‖(r : ℂ) * expLocalRemainderFifth (x / Real.sqrt (blocks3SaddleBReal r)) +
                      (((r ^ 2 / 2 : ℝ) : ℂ) *
                        expLocalRemainderFifth (2 * (x / Real.sqrt (blocks3SaddleBReal r))))‖ +
                        ‖(((r ^ 3 / 6 : ℝ) : ℂ) *
                          expLocalRemainderFifth (3 * (x / Real.sqrt (blocks3SaddleBReal r))))‖ :=
                    norm_add_le _ _
              _ ≤ (‖(r : ℂ) * expLocalRemainderFifth (x / Real.sqrt (blocks3SaddleBReal r))‖ +
                    ‖(((r ^ 2 / 2 : ℝ) : ℂ) *
                      expLocalRemainderFifth (2 * (x / Real.sqrt (blocks3SaddleBReal r))))‖) +
                    ‖(((r ^ 3 / 6 : ℝ) : ℂ) *
                      expLocalRemainderFifth (3 * (x / Real.sqrt (blocks3SaddleBReal r))))‖ :=
                  add_le_add (norm_add_le _ _) (le_refl _)
              _ = _ := by ring
      _ ≤ r * (Real.exp 3 * (A * y) ^ 5) +
            (r ^ 2 / 2) * (Real.exp 3 * (2 * A * y) ^ 5) +
              (r ^ 3 / 6) * (Real.exp 3 * (3 * A * y) ^ 5) := by
          gcongr
          · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
            exact mul_le_mul_of_nonneg_left
              (hrem1.trans (mul_le_mul_of_nonneg_left hθ5_le (Real.exp_pos 3).le))
              hr0
          · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
            have hcoef : 0 ≤ r ^ 2 / 2 := by positivity
            rw [abs_of_nonneg hcoef]
            exact mul_le_mul_of_nonneg_left
              (hrem2.trans (mul_le_mul_of_nonneg_left h2θ5_le (Real.exp_pos 3).le))
              hcoef
          · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
            have hcoef : 0 ≤ r ^ 3 / 6 := by positivity
            rw [abs_of_nonneg hcoef]
            exact mul_le_mul_of_nonneg_left
              (hrem3.trans (mul_le_mul_of_nonneg_left h3θ5_le (Real.exp_pos 3).le))
              hcoef
  calc
    ‖blocks3ScaledRemainder r x‖
        ≤ r * (Real.exp 3 * (A * y) ^ 5) +
          (r ^ 2 / 2) * (Real.exp 3 * (2 * A * y) ^ 5) +
            (r ^ 3 / 6) * (Real.exp 3 * (3 * A * y) ^ 5) := hmain
    _ ≤ blocks3LocalTaylorConst * D * y ^ 5 := by
      have hterm1 : r * (Real.exp 3 * (A * y) ^ 5) ≤
          Real.exp 3 * D * y ^ 5 := by
        calc
          r * (Real.exp 3 * (A * y) ^ 5)
              = Real.exp 3 * (r * A ^ 5) * y ^ 5 := by ring
          _ ≤ Real.exp 3 * D * y ^ 5 := by
            gcongr
      have hterm2 : (r ^ 2 / 2) * (Real.exp 3 * (2 * A * y) ^ 5) ≤
          16 * Real.exp 3 * D * y ^ 5 := by
        calc
          (r ^ 2 / 2) * (Real.exp 3 * (2 * A * y) ^ 5)
              = 16 * Real.exp 3 * (r ^ 2 * A ^ 5) * y ^ 5 := by ring
          _ ≤ 16 * Real.exp 3 * D * y ^ 5 := by
            gcongr
      have hterm3 : (r ^ 3 / 6) * (Real.exp 3 * (3 * A * y) ^ 5) ≤
          100 * Real.exp 3 * D * y ^ 5 := by
        calc
          (r ^ 3 / 6) * (Real.exp 3 * (3 * A * y) ^ 5)
              = (81 / 2 : ℝ) * Real.exp 3 * (r ^ 3 * A ^ 5) * y ^ 5 := by ring
          _ ≤ 100 * Real.exp 3 * D * y ^ 5 := by
            gcongr
            norm_num
      unfold blocks3LocalTaylorConst
      calc
        r * (Real.exp 3 * (A * y) ^ 5) +
            (r ^ 2 / 2) * (Real.exp 3 * (2 * A * y) ^ 5) +
              (r ^ 3 / 6) * (Real.exp 3 * (3 * A * y) ^ 5)
            ≤ Real.exp 3 * D * y ^ 5 +
                16 * Real.exp 3 * D * y ^ 5 +
                  100 * Real.exp 3 * D * y ^ 5 :=
              add_le_add (add_le_add hterm1 hterm2) hterm3
        _ ≤ 10000 * Real.exp 3 * D * y ^ 5 := by
          have hnonneg : 0 ≤ Real.exp 3 * D * y ^ 5 := by positivity
          nlinarith

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

private def blocks3GaussianDom (x : ℝ) : ℝ :=
  Real.exp (-(x ^ 2) / 2) *
    (|x| ^ 5 + |x| ^ 6 + |x| ^ 7 + |x| ^ 8 + |x| ^ 9 + |x| ^ 10 +
      |x| ^ 11 + |x| ^ 12 + |x| ^ 13 + |x| ^ 14 + |x| ^ 15)

private lemma blocks3GaussianDom_nonneg (x : ℝ) : 0 ≤ blocks3GaussianDom x := by
  unfold blocks3GaussianDom
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

private lemma blocks3GaussianDom_integrable : Integrable blocks3GaussianDom := by
  let g : ℕ → ℝ → ℝ := fun k x => Real.exp (-(x ^ 2) / 2) * |x| ^ k
  have hsum :
      Integrable (fun x : ℝ =>
        g 5 x + g 6 x + g 7 x + g 8 x + g 9 x + g 10 x +
          g 11 x + g 12 x + g 13 x + g 14 x + g 15 x) := by
    simpa [g, add_assoc] using
      ((((((((((gaussian_abs_monomial_integrable 5).add
        (gaussian_abs_monomial_integrable 6)).add
        (gaussian_abs_monomial_integrable 7)).add
        (gaussian_abs_monomial_integrable 8)).add
        (gaussian_abs_monomial_integrable 9)).add
        (gaussian_abs_monomial_integrable 10)).add
        (gaussian_abs_monomial_integrable 11)).add
        (gaussian_abs_monomial_integrable 12)).add
        (gaussian_abs_monomial_integrable 13)).add
        (gaussian_abs_monomial_integrable 14)).add
        (gaussian_abs_monomial_integrable 15)
  convert hsum using 1
  ext x
  unfold blocks3GaussianDom
  dsimp [g]
  ring_nf

private lemma blocks3GaussianDom_integral_nonneg :
    0 ≤ ∫ x : ℝ, blocks3GaussianDom x := by
  exact integral_nonneg (fun x => blocks3GaussianDom_nonneg x)

private def blocks3LocalL1Const : ℝ :=
  27 * Real.exp 1 * (20 + blocks3LocalTaylorConst) ^ 3 + blocks3LocalTaylorConst +
    6 * (10 + blocks3LocalTaylorConst) * (30 + blocks3LocalTaylorConst)

private lemma blocks3LocalL1Const_pos : 0 < blocks3LocalL1Const := by
  unfold blocks3LocalL1Const blocks3LocalTaylorConst
  positivity

private lemma blocks3_local_integrand_bound {r x : ℝ}
    (hr : 1 ≤ r)
    (hθ : |x / Real.sqrt (blocks3SaddleBReal r)| ≤ 1)
    (hWnorm : ‖blocks3LocalExponent r (x / Real.sqrt (blocks3SaddleBReal r))‖ ≤ 1) :
    ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleLocalRatio blocks3Fun blocks3SaddleAReal blocks3SaddleBReal r
            (x / Real.sqrt (blocks3SaddleBReal r)) -
          saddleSecondPoly blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real r x)‖
      ≤ blocks3LocalL1Const * r ^ (-(9 / 2 : ℝ)) * blocks3GaussianDom x := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hr0 : 0 ≤ r := hrpos.le
  have hbpos : 0 < blocks3SaddleBReal r := blocks3SaddleBReal_pos_of_ge_one hr
  let C : ℂ := blocks3ScaledCubic r x
  let Q : ℂ := blocks3ScaledQuartic r x
  let R : ℂ := blocks3ScaledRemainder r x
  let W : ℂ := blocks3LocalExponent r (x / Real.sqrt (blocks3SaddleBReal r))
  let y : ℝ := |x|
  let A : ℝ := r ^ (-(3 / 2 : ℝ))
  let B : ℝ := r ^ (-(3 : ℝ))
  let D : ℝ := r ^ (-(9 / 2 : ℝ))
  let K : ℝ := blocks3LocalTaylorConst
  let S : ℝ := 10 * y ^ 3 + 10 * y ^ 4 + K * y ^ 5
  let T : ℝ := (10 * y ^ 4 + K * y ^ 5) * (20 * y ^ 3 + 10 * y ^ 4 + K * y ^ 5)
  let G : ℝ := y ^ 5 + y ^ 6 + y ^ 7 + y ^ 8 + y ^ 9 + y ^ 10 +
    y ^ 11 + y ^ 12 + y ^ 13 + y ^ 14 + y ^ 15
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    exact blocks3LocalTaylorConst_pos.le
  have hy0 : 0 ≤ y := by
    dsimp [y]
    exact abs_nonneg x
  have hA_nonneg : 0 ≤ A := by dsimp [A]; positivity
  have hB_nonneg : 0 ≤ B := by dsimp [B]; positivity
  have hD_nonneg : 0 ≤ D := by dsimp [D]; positivity
  have hA_le_one : A ≤ 1 := by
    dsimp [A]
    rw [Real.rpow_neg hr0]
    have hbase : 1 ≤ r ^ (3 / 2 : ℝ) := by
      calc
        (1 : ℝ) = (1 : ℝ) ^ (3 / 2 : ℝ) := by rw [Real.one_rpow]
        _ ≤ r ^ (3 / 2 : ℝ) :=
          Real.rpow_le_rpow zero_le_one hr (by norm_num : (0 : ℝ) ≤ 3 / 2)
    exact inv_le_one_of_one_le₀ hbase
  have hA_mul_A : A * A = B := by
    dsimp [A, B]
    rw [← Real.rpow_add hrpos]
    norm_num
  have hA_mul_B : A * B = D := by
    dsimp [A, B, D]
    rw [← Real.rpow_add hrpos]
    norm_num
  have hB_le_A : B ≤ A := by
    rw [← hA_mul_A]
    exact mul_le_of_le_one_right hA_nonneg hA_le_one
  have hB_le_one : B ≤ 1 := hB_le_A.trans hA_le_one
  have hD_le_A : D ≤ A := by
    rw [← hA_mul_B]
    exact mul_le_of_le_one_right hA_nonneg hB_le_one
  have hD_le_B : D ≤ B := by
    rw [← hA_mul_B]
    exact mul_le_of_le_one_left hB_nonneg hA_le_one
  have hWsplit : W = C + Q + R := by
    dsimp [W, C, Q, R]
    exact blocks3LocalExponent_scaled_split hbpos
  have hP :
      saddleSecondPoly blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real r x =
        1 + C + Q + C ^ 2 / 2 := by
    dsimp [C, Q]
    exact blocks3_saddleSecondPoly_eq_scaled_terms hbpos
  have herr := complex_exp_second_error_bound C Q R W hWsplit (by simpa [W] using hWnorm)
  have hC : ‖C‖ ≤ 10 * A * y ^ 3 := by
    dsimp [C, A, y]
    simpa [mul_assoc] using blocks3ScaledCubic_norm_le (r := r) (x := x) hr
  have hQ_B : ‖Q‖ ≤ 10 * B * y ^ 4 := by
    dsimp [Q, B, y]
    simpa [mul_assoc] using blocks3ScaledQuartic_norm_le (r := r) (x := x) hr
  have hQ_A : ‖Q‖ ≤ 10 * A * y ^ 4 := by
    exact hQ_B.trans (by gcongr)
  have hR_D : ‖R‖ ≤ K * D * y ^ 5 := by
    dsimp [R, K, D, y]
    simpa [mul_assoc] using blocks3ScaledRemainder_norm_le (r := r) (x := x) hr hθ
  have hR_A : ‖R‖ ≤ K * A * y ^ 5 := by
    exact hR_D.trans (by gcongr)
  have hR_B : ‖R‖ ≤ K * B * y ^ 5 := by
    exact hR_D.trans (by gcongr)
  have hWpoly : ‖W‖ ≤ A * S := by
    calc
      ‖W‖ = ‖C + Q + R‖ := by rw [hWsplit]
      _ ≤ ‖C‖ + ‖Q‖ + ‖R‖ := by
        calc
          ‖C + Q + R‖ ≤ ‖C + Q‖ + ‖R‖ := norm_add_le _ _
          _ ≤ (‖C‖ + ‖Q‖) + ‖R‖ := add_le_add (norm_add_le _ _) (le_refl _)
          _ = ‖C‖ + ‖Q‖ + ‖R‖ := by ring
      _ ≤ 10 * A * y ^ 3 + 10 * A * y ^ 4 + K * A * y ^ 5 :=
        add_le_add (add_le_add hC hQ_A) hR_A
      _ = A * S := by
        dsimp [S]
        ring
  have hWcube :
      Real.exp 1 * ‖W‖ ^ 3 ≤ Real.exp 1 * D * S ^ 3 := by
    have hA_cube : A ^ 3 = D := by
      dsimp [A, D]
      rw [(Real.rpow_mul_natCast hr0 (-(3 / 2 : ℝ)) 3).symm]
      norm_num
    calc
      Real.exp 1 * ‖W‖ ^ 3 ≤ Real.exp 1 * (A * S) ^ 3 := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg W) hWpoly 3) (Real.exp_pos 1).le
      _ = Real.exp 1 * D * S ^ 3 := by
        rw [mul_pow, hA_cube]
        ring
  have hQR : ‖Q‖ + ‖R‖ ≤ B * (10 * y ^ 4 + K * y ^ 5) := by
    calc
      ‖Q‖ + ‖R‖ ≤ 10 * B * y ^ 4 + K * B * y ^ 5 := add_le_add hQ_B hR_B
      _ = B * (10 * y ^ 4 + K * y ^ 5) := by ring
  have hCQR : 2 * ‖C‖ + ‖Q‖ + ‖R‖ ≤ A * (20 * y ^ 3 + 10 * y ^ 4 + K * y ^ 5) := by
    calc
      2 * ‖C‖ + ‖Q‖ + ‖R‖
          ≤ 2 * (10 * A * y ^ 3) + 10 * A * y ^ 4 + K * A * y ^ 5 := by
            exact add_le_add (add_le_add
              (mul_le_mul_of_nonneg_left hC (by norm_num : (0 : ℝ) ≤ 2)) hQ_A) hR_A
      _ = A * (20 * y ^ 3 + 10 * y ^ 4 + K * y ^ 5) := by ring
  have hprod :
      (‖Q‖ + ‖R‖) * (2 * ‖C‖ + ‖Q‖ + ‖R‖) ≤ D * T := by
    calc
      (‖Q‖ + ‖R‖) * (2 * ‖C‖ + ‖Q‖ + ‖R‖)
          ≤ (B * (10 * y ^ 4 + K * y ^ 5)) *
              (A * (20 * y ^ 3 + 10 * y ^ 4 + K * y ^ 5)) := by
            have hupper_nonneg : 0 ≤ B * (10 * y ^ 4 + K * y ^ 5) := by
              positivity
            exact mul_le_mul hQR hCQR (by positivity) hupper_nonneg
      _ = D * T := by
        dsimp [T]
        rw [show B * (10 * y ^ 4 + K * y ^ 5) *
              (A * (20 * y ^ 3 + 10 * y ^ 4 + K * y ^ 5)) =
              (A * B) * ((10 * y ^ 4 + K * y ^ 5) *
                (20 * y ^ 3 + 10 * y ^ 4 + K * y ^ 5)) by ring]
        rw [hA_mul_B]
  have hpoly :
      Real.exp 1 * S ^ 3 + K * y ^ 5 + T ≤ blocks3LocalL1Const * G := by
    have hK20_nonneg : 0 ≤ 20 + K := by positivity
    have hK10_nonneg : 0 ≤ 10 + K := by positivity
    have hK30_nonneg : 0 ≤ 30 + K := by positivity
    have hG_nonneg : 0 ≤ G := by
      dsimp [G]
      positivity
    have hy5_le_G : y ^ 5 ≤ G := by
      dsimp [G]
      nlinarith [pow_nonneg hy0 6, pow_nonneg hy0 7, pow_nonneg hy0 8,
        pow_nonneg hy0 9, pow_nonneg hy0 10, pow_nonneg hy0 11,
        pow_nonneg hy0 12, pow_nonneg hy0 13, pow_nonneg hy0 14,
        pow_nonneg hy0 15]
    have hcube_support :
        (y ^ 3 + y ^ 4 + y ^ 5) ^ 3 ≤ 27 * G := by
      dsimp [G]
      ring_nf
      nlinarith [pow_nonneg hy0 5, pow_nonneg hy0 6, pow_nonneg hy0 7,
        pow_nonneg hy0 8, pow_nonneg hy0 9, pow_nonneg hy0 10,
        pow_nonneg hy0 11, pow_nonneg hy0 12, pow_nonneg hy0 13,
        pow_nonneg hy0 14, pow_nonneg hy0 15]
    have hprod_support :
        (y ^ 4 + y ^ 5) * (y ^ 3 + y ^ 4 + y ^ 5) ≤ 6 * G := by
      dsimp [G]
      ring_nf
      nlinarith [pow_nonneg hy0 5, pow_nonneg hy0 6, pow_nonneg hy0 7,
        pow_nonneg hy0 8, pow_nonneg hy0 9, pow_nonneg hy0 10]
    have hS_le : S ≤ (20 + K) * (y ^ 3 + y ^ 4 + y ^ 5) := by
      dsimp [S]
      calc
        10 * y ^ 3 + 10 * y ^ 4 + K * y ^ 5
            ≤ (20 + K) * y ^ 3 + (20 + K) * y ^ 4 + (20 + K) * y ^ 5 := by
              gcongr
              · linarith
              · linarith
              · linarith
        _ = (20 + K) * (y ^ 3 + y ^ 4 + y ^ 5) := by ring
    have hS_cube :
        S ^ 3 ≤ (20 + K) ^ 3 * (27 * G) := by
      calc
        S ^ 3 ≤ ((20 + K) * (y ^ 3 + y ^ 4 + y ^ 5)) ^ 3 :=
          pow_le_pow_left₀ (by positivity) hS_le 3
        _ = (20 + K) ^ 3 * (y ^ 3 + y ^ 4 + y ^ 5) ^ 3 := by ring
        _ ≤ (20 + K) ^ 3 * (27 * G) :=
          mul_le_mul_of_nonneg_left hcube_support (pow_nonneg hK20_nonneg 3)
    have hT_le :
        T ≤ (10 + K) * (30 + K) * (6 * G) := by
      have hleft : 10 * y ^ 4 + K * y ^ 5 ≤ (10 + K) * (y ^ 4 + y ^ 5) := by
        calc
          10 * y ^ 4 + K * y ^ 5 ≤ (10 + K) * y ^ 4 + (10 + K) * y ^ 5 := by
            gcongr
            · linarith
            · linarith
          _ = (10 + K) * (y ^ 4 + y ^ 5) := by ring
      have hright :
          20 * y ^ 3 + 10 * y ^ 4 + K * y ^ 5 ≤
            (30 + K) * (y ^ 3 + y ^ 4 + y ^ 5) := by
        calc
          20 * y ^ 3 + 10 * y ^ 4 + K * y ^ 5
              ≤ (30 + K) * y ^ 3 + (30 + K) * y ^ 4 + (30 + K) * y ^ 5 := by
                gcongr
                · linarith
                · linarith
                · linarith
          _ = (30 + K) * (y ^ 3 + y ^ 4 + y ^ 5) := by ring
      calc
        T ≤ ((10 + K) * (y ^ 4 + y ^ 5)) *
              ((30 + K) * (y ^ 3 + y ^ 4 + y ^ 5)) := by
          dsimp [T]
          exact mul_le_mul hleft hright (by positivity) (by positivity)
        _ = (10 + K) * (30 + K) *
              ((y ^ 4 + y ^ 5) * (y ^ 3 + y ^ 4 + y ^ 5)) := by ring
        _ ≤ (10 + K) * (30 + K) * (6 * G) := by
          gcongr
    calc
      Real.exp 1 * S ^ 3 + K * y ^ 5 + T
          ≤ Real.exp 1 * ((20 + K) ^ 3 * (27 * G)) + K * G +
              (10 + K) * (30 + K) * (6 * G) := by
            exact add_le_add (add_le_add
              (mul_le_mul_of_nonneg_left hS_cube (Real.exp_pos 1).le)
              (mul_le_mul_of_nonneg_left hy5_le_G hK_nonneg)) hT_le
      _ = (27 * Real.exp 1 * (20 + K) ^ 3 + K +
            6 * (10 + K) * (30 + K)) * G := by ring
      _ = blocks3LocalL1Const * G := by
        dsimp [K]
        unfold blocks3LocalL1Const
        ring
  have hdiff :
      ‖Complex.exp W - (1 + C + Q + C ^ 2 / 2)‖ ≤
        blocks3LocalL1Const * D * G := by
    calc
      ‖Complex.exp W - (1 + C + Q + C ^ 2 / 2)‖
          ≤ Real.exp 1 * ‖W‖ ^ 3 + ‖R‖ +
              (‖Q‖ + ‖R‖) * (2 * ‖C‖ + ‖Q‖ + ‖R‖) := herr
      _ ≤ Real.exp 1 * D * S ^ 3 + K * D * y ^ 5 + D * T := by
        exact add_le_add (add_le_add hWcube hR_D) hprod
      _ = D * (Real.exp 1 * S ^ 3 + K * y ^ 5 + T) := by ring
      _ ≤ D * (blocks3LocalL1Const * G) :=
        mul_le_mul_of_nonneg_left hpoly hD_nonneg
      _ = blocks3LocalL1Const * D * G := by ring
  rw [blocks3_saddleLocalRatio_eq]
  rw [hP]
  change
    ‖Complex.exp (-(x ^ 2) / 2) *
        (Complex.exp W - (1 + C + Q + C ^ 2 / 2))‖ ≤
      blocks3LocalL1Const * D * blocks3GaussianDom x
  rw [norm_mul]
  have hgauss :
      ‖Complex.exp (-(x ^ 2) / 2)‖ = Real.exp (-(x ^ 2) / 2) := by
    rw [Complex.norm_exp]
    congr 1
    simp [pow_two]
  rw [hgauss]
  unfold blocks3GaussianDom
  dsimp [D, G, y]
  calc
    Real.exp (-(x ^ 2) / 2) *
        ‖Complex.exp W - (1 + C + Q + C ^ 2 / 2)‖
        ≤ Real.exp (-(x ^ 2) / 2) * (blocks3LocalL1Const * D * G) :=
          mul_le_mul_of_nonneg_left hdiff (Real.exp_pos _).le
    _ = blocks3LocalL1Const * D *
        (Real.exp (-(x ^ 2) / 2) *
          (|x| ^ 5 + |x| ^ 6 + |x| ^ 7 + |x| ^ 8 + |x| ^ 9 + |x| ^ 10 +
            |x| ^ 11 + |x| ^ 12 + |x| ^ 13 + |x| ^ 14 + |x| ^ 15)) := by
      ring

private lemma blocks3_local_integrand_continuous (r : ℝ) :
    Continuous fun x : ℝ =>
      ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleLocalRatio blocks3Fun blocks3SaddleAReal blocks3SaddleBReal r
            (x / Real.sqrt (blocks3SaddleBReal r)) -
          saddleSecondPoly blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real r x)‖ := by
  have h :
      Continuous fun x : ℝ =>
        ‖Complex.exp (-(x ^ 2) / 2) *
          (Complex.exp (blocks3LocalExponent r (x / Real.sqrt (blocks3SaddleBReal r))) -
            saddleSecondPoly blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real r x)‖ := by
    unfold blocks3LocalExponent ExpStirling.expLocalRemainder saddleSecondPoly
    fun_prop
  simpa [blocks3_saddleLocalRatio_eq] using h

private lemma blocks3GaussianDom_continuous : Continuous blocks3GaussianDom := by
  unfold blocks3GaussianDom
  fun_prop

private lemma blocks3GaussianDom_window_le_integral {L : ℝ} (hL : 0 ≤ L) :
    (∫ x in -L..L, blocks3GaussianDom x) ≤ ∫ x : ℝ, blocks3GaussianDom x := by
  have hle : -L ≤ L := by linarith
  rw [intervalIntegral.integral_of_le hle]
  exact setIntegral_le_integral blocks3GaussianDom_integrable
    (Eventually.of_forall blocks3GaussianDom_nonneg)

theorem blocks3_local_second_L1 :
    Tendsto
      (fun r : ℝ =>
        (∫ x in -(blocks3SaddleDeltaReal r * Real.sqrt (blocks3SaddleBReal r))..
          (blocks3SaddleDeltaReal r * Real.sqrt (blocks3SaddleBReal r)),
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleLocalRatio blocks3Fun blocks3SaddleAReal blocks3SaddleBReal r
                (x / Real.sqrt (blocks3SaddleBReal r)) -
              saddleSecondPoly blocks3SaddleBReal blocks3SaddleB3Real
                blocks3SaddleB4Real r x)‖) /
          blocks3SecondCorrScale r)
      atTop (𝓝 0) := by
  let M : ℝ := ∫ x : ℝ, blocks3GaussianDom x
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact blocks3GaussianDom_integral_nonneg
  have hupper_tendsto :
      Tendsto
        (fun r : ℝ => blocks3LocalL1Const * M * r ^ (-(3 / 2 : ℝ)))
        atTop (𝓝 0) := by
    have hpow : Tendsto (fun r : ℝ => r ^ (-(3 / 2 : ℝ))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 2)
    simpa [mul_assoc] using hpow.const_mul (blocks3LocalL1Const * M)
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
            (saddleLocalRatio blocks3Fun blocks3SaddleAReal blocks3SaddleBReal r
                (x / Real.sqrt (blocks3SaddleBReal r)) -
              saddleSecondPoly blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real r x)‖ :=
      intervalIntegral.integral_nonneg hle (fun _ _ => norm_nonneg _)
    exact div_nonneg hint_nonneg hcorr.le
  · filter_upwards [eventually_ge_atTop (1 : ℝ), blocks3_delta_le_one_eventually,
      blocks3_local_exponent_norm_le_eventually,
      blocks3LocalBound_tendsto_zero.eventually_le_const zero_lt_one,
      blocks3SecondCorrScale_pos_eventually] with
      r hr hδle hloc hlocSmall hcorrPos
    let L : ℝ := blocks3SaddleDeltaReal r * Real.sqrt (blocks3SaddleBReal r)
    let F : ℝ → ℝ := fun x =>
      ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleLocalRatio blocks3Fun blocks3SaddleAReal blocks3SaddleBReal r
            (x / Real.sqrt (blocks3SaddleBReal r)) -
          saddleSecondPoly blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real r x)‖
    let H : ℝ → ℝ := fun x =>
      (blocks3LocalL1Const * r ^ (-(9 / 2 : ℝ))) * blocks3GaussianDom x
    have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
    have hbpos : 0 < blocks3SaddleBReal r := blocks3SaddleBReal_pos_of_ge_one hr
    have hsqrt_pos : 0 < Real.sqrt (blocks3SaddleBReal r) := Real.sqrt_pos.mpr hbpos
    have hLnonneg : 0 ≤ L := by
      dsimp [L, blocks3SaddleDeltaReal]
      positivity
    have hle : -L ≤ L := by linarith
    have hpoint : ∀ x ∈ Set.Icc (-L) L, F x ≤ H x := by
      intro x hx
      have hxabs : |x| ≤ L := by
        exact abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
      have hθδ : |x / Real.sqrt (blocks3SaddleBReal r)| ≤ blocks3SaddleDeltaReal r := by
        rw [abs_div, abs_of_pos hsqrt_pos]
        calc
          |x| / Real.sqrt (blocks3SaddleBReal r) ≤
              L / Real.sqrt (blocks3SaddleBReal r) :=
            div_le_div_of_nonneg_right hxabs hsqrt_pos.le
          _ = blocks3SaddleDeltaReal r := by
            dsimp [L]
            field_simp [hsqrt_pos.ne']
      have hθone : |x / Real.sqrt (blocks3SaddleBReal r)| ≤ 1 := hθδ.trans hδle
      have hWnorm :
          ‖blocks3LocalExponent r (x / Real.sqrt (blocks3SaddleBReal r))‖ ≤ 1 :=
        (hloc (x / Real.sqrt (blocks3SaddleBReal r)) hθδ).trans hlocSmall
      have hb := blocks3_local_integrand_bound hr hθone hWnorm
      dsimp [F, H]
      exact hb
    have hFint : IntervalIntegrable F volume (-L) L := by
      exact (blocks3_local_integrand_continuous r).intervalIntegrable _ _
    have hHint : IntervalIntegrable H volume (-L) L := by
      exact (blocks3GaussianDom_continuous.const_mul
        (blocks3LocalL1Const * r ^ (-(9 / 2 : ℝ)))).intervalIntegrable _ _
    have hIntBound :
        (∫ x in -L..L, F x) ≤
          (blocks3LocalL1Const * r ^ (-(9 / 2 : ℝ))) * M := by
      have hconst_nonneg :
          0 ≤ blocks3LocalL1Const * r ^ (-(9 / 2 : ℝ)) :=
        mul_nonneg blocks3LocalL1Const_pos.le (by positivity)
      calc
        (∫ x in -L..L, F x) ≤ ∫ x in -L..L, H x :=
          intervalIntegral.integral_mono_on hle hFint hHint hpoint
        _ = (blocks3LocalL1Const * r ^ (-(9 / 2 : ℝ))) *
              (∫ x in -L..L, blocks3GaussianDom x) := by
          dsimp [H]
          rw [intervalIntegral.integral_const_mul]
        _ ≤ (blocks3LocalL1Const * r ^ (-(9 / 2 : ℝ))) * M := by
          exact mul_le_mul_of_nonneg_left
            (by dsimp [M]; exact blocks3GaussianDom_window_le_integral hLnonneg)
            hconst_nonneg
    have hnum_nonneg :
        0 ≤ (blocks3LocalL1Const * r ^ (-(9 / 2 : ℝ))) * M :=
      mul_nonneg
        (mul_nonneg blocks3LocalL1Const_pos.le (by positivity)) hM_nonneg
    have hmain :
        (∫ x in -L..L, F x) / blocks3SecondCorrScale r ≤
          ((blocks3LocalL1Const * r ^ (-(9 / 2 : ℝ))) * M) /
            blocks3SecondCorrScale r := by
      exact div_le_div_of_nonneg_right hIntBound hcorrPos.le
    have hpow_div :
        r ^ (-(9 / 2 : ℝ)) / blocks3SecondCorrScale r =
          r ^ (-(3 / 2 : ℝ)) := by
      unfold blocks3SecondCorrScale
      rw [div_eq_mul_inv]
      have hneg3 : r ^ (-(3 : ℝ)) = (r ^ (3 : ℝ))⁻¹ :=
        Real.rpow_neg hrpos.le (3 : ℝ)
      rw [hneg3, inv_inv]
      rw [← Real.rpow_add hrpos]
      norm_num
    calc
      ((∫ x in -(blocks3SaddleDeltaReal r * Real.sqrt (blocks3SaddleBReal r))..
          (blocks3SaddleDeltaReal r * Real.sqrt (blocks3SaddleBReal r)),
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleLocalRatio blocks3Fun blocks3SaddleAReal blocks3SaddleBReal r
                (x / Real.sqrt (blocks3SaddleBReal r)) -
              saddleSecondPoly blocks3SaddleBReal blocks3SaddleB3Real
                blocks3SaddleB4Real r x)‖) /
          blocks3SecondCorrScale r)
          = (∫ x in -L..L, F x) / blocks3SecondCorrScale r := by rfl
      _ ≤ ((blocks3LocalL1Const * r ^ (-(9 / 2 : ℝ))) * M) /
            blocks3SecondCorrScale r := hmain
      _ = blocks3LocalL1Const * M * r ^ (-(3 / 2 : ℝ)) := by
        rw [show ((blocks3LocalL1Const * r ^ (-(9 / 2 : ℝ))) * M) /
            blocks3SecondCorrScale r =
            blocks3LocalL1Const * M *
              (r ^ (-(9 / 2 : ℝ)) / blocks3SecondCorrScale r) by ring]
        rw [hpow_div]

/-- The produced second-order H-admissible instance for blocks of size at most three. -/
def blocks3SecondOrderHAdmissible : SecondOrderHAdmissible blocks3HAdmissible where
  b3 := blocks3SaddleB3Real
  b4 := blocks3SaddleB4Real
  corrScale := blocks3SecondCorrScale
  corrScale_pos := by
    simpa [blocks3HAdmissible] using blocks3SecondCorrScale_pos_eventually
  corrScale_tendsto_zero := by
    simpa [blocks3HAdmissible] using blocks3SecondCorrScale_tendsto_zero
  corrScale_dominates_correction := by
    refine ⟨1000000, by norm_num, ?_⟩
    simpa [blocks3HAdmissible] using blocks3_saddleCorrectionScale_le_secondCorrScale_eventually
  local_second_L1 := by
    simpa [blocks3HAdmissible] using blocks3_local_second_L1
  tail_second_uniform := by
    simpa [blocks3HAdmissible] using blocks3_tail_second_uniform

/-- Abstract second-order saddle theorem specialized to the blocks-≤3 saddle. -/
theorem blocks3_coeff_secondOrder_saddle_from_HAdmissible :
    (fun n : ℕ =>
      blocks3Series.coeff n / blocks3SecondOrderSaddleScale n -
        (1 + (blocks3SecondCorrectionAtSaddle n : ℂ)))
      =o[atTop]
    (fun n : ℕ => (blocks3SecondCorrScale (blocks3SaddleRadius n) : ℂ)) := by
  have h :=
    coeff_secondOrder_saddle
      blocks3HAdmissible blocks3SecondOrderHAdmissible blocks3HAdmissibleSaddleSequence
  simpa [blocks3SecondOrderSaddleScale, blocks3SecondCorrectionAtSaddle,
    HAdmissible.B, blocks3HAdmissible, blocks3HAdmissibleSaddleSequence,
    blocks3SecondOrderHAdmissible, blocks3SecondCorrScale] using h

/--
Second-order saddle ratio for set partitions with blocks of size at most three:
`B₃(n)/n! = saddleScale_n * (1 + δ_n + o(r_n^{-3}))`, where
`δ_n = b₄(r_n)/(8 b(r_n)^2) - 5 b₃(r_n)^2/(24 b(r_n)^3)`.
-/
theorem blocks3_number_over_factorial_secondOrder_saddle :
    (fun n : ℕ => blocks3SecondOrderNumberError n)
      =o[atTop]
    (fun n : ℕ => (blocks3SecondCorrScale (blocks3SaddleRadius n) : ℂ)) := by
  simpa [blocks3SecondOrderNumberError, blocks3SecondOrderSaddleScale,
    blocks3SecondCorrectionAtSaddle, PowerSeries.coeff_toFMLS, blocks3Carrier_coeff,
    blocks3CoeffR] using blocks3_coeff_secondOrder_saddle_from_HAdmissible

end Blocks3HAdmissible
