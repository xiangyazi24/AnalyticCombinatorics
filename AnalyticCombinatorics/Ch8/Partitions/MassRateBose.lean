import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.MassRateExpBounds

/-!
# Mass-rate campaign: boseReg0 bounds (R10 bricks 4–6)

The rational form of `boseReg0`, boundedness near zero (`|boseReg0| ≤ 4` on `(0,1]`, via
the exact numerator identity `x²eˣ − (eˣ−1)² = x⁴/4 − 2xδ − δ²` with `|δ| ≤ x³`), and the
tail bound `|boseReg0| ≤ 4e^{−x} + 1/x²` for `x ≥ 1`.  Opus-authored.
-/

set_option maxHeartbeats 800000

noncomputable section

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- The rational form of `boseReg0` over a common denominator. -/
lemma boseReg0_eq_small_num {x : ℝ} (hx : 0 < x) :
    boseReg0 x = (x ^ 2 * Real.exp x - (Real.exp x - 1) ^ 2) /
      (x ^ 2 * (Real.exp x - 1) ^ 2) := by
  have hy : x ≤ Real.exp x - 1 := by linarith [Real.add_one_le_exp x]
  have hypos : 0 < Real.exp x - 1 := by linarith
  rw [boseReg0, boseKernel_eq_exp_form hx]
  field_simp

/-- `|boseReg0| ≤ 4` on `(0,1]`. -/
lemma boseReg0_bdd_near_zero {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    |boseReg0 x| ≤ 4 := by
  set δ : ℝ := Real.exp x - 1 - x - x ^ 2 / 2 with hδdef
  have hδ : |δ| ≤ x ^ 3 := by
    rw [hδdef]
    have := exp_sub_one_sub_self_sq_bound hx0.le hx1
    convert this using 2
  have hδlo := (abs_le.mp hδ).1
  have hδhi := (abs_le.mp hδ).2
  have hy : x ≤ Real.exp x - 1 := by linarith [Real.add_one_le_exp x]
  have hypos : 0 < Real.exp x - 1 := by linarith
  -- exact numerator identity
  have hnum_eq : x ^ 2 * Real.exp x - (Real.exp x - 1) ^ 2
      = x ^ 4 / 4 - 2 * x * δ - δ ^ 2 := by
    rw [hδdef]
    ring
  have hx3 : x ^ 3 ≤ x ^ 2 := by nlinarith [hx0.le]
  have hnum_abs : |x ^ 2 * Real.exp x - (Real.exp x - 1) ^ 2| ≤ 4 * x ^ 4 := by
    rw [hnum_eq, abs_le]
    have hδsq : δ ^ 2 ≤ x ^ 6 := by nlinarith [hδlo, hδhi]
    have hx6 : x ^ 6 ≤ x ^ 4 := by nlinarith [hx0.le, hx1, pow_pos hx0 4]
    have hxδhi : x * δ ≤ x * x ^ 3 := mul_le_mul_of_nonneg_left hδhi hx0.le
    have hxδlo : x * (-(x ^ 3)) ≤ x * δ := mul_le_mul_of_nonneg_left hδlo hx0.le
    constructor
    · nlinarith [hxδhi, hxδlo, hx0.le, hδsq, hx6]
    · nlinarith [hxδhi, hxδlo, hx0.le, hδsq, hx6, sq_nonneg δ]
  have hsq : x ^ 2 ≤ (Real.exp x - 1) ^ 2 := by nlinarith [hy, hx0.le]
  have hden_ge : x ^ 4 ≤ x ^ 2 * (Real.exp x - 1) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ x ^ 2)]
  have hden_pos : 0 < x ^ 2 * (Real.exp x - 1) ^ 2 := by positivity
  rw [boseReg0_eq_small_num hx0, abs_div,
    abs_of_pos hden_pos]
  calc |x ^ 2 * Real.exp x - (Real.exp x - 1) ^ 2| / (x ^ 2 * (Real.exp x - 1) ^ 2)
      ≤ (4 * x ^ 4) / x ^ 4 :=
        div_le_div₀ (by positivity) hnum_abs (by positivity) hden_ge
    _ = 4 := by
        field_simp

/-- Tail bound: `|boseReg0 x| ≤ 4e^{−x} + 1/x²` for `x ≥ 1`. -/
lemma boseReg0_tail_bound {x : ℝ} (hx : 1 ≤ x) :
    |boseReg0 x| ≤ 4 * Real.exp (-x) + 1 / x ^ 2 := by
  have hxpos : (0 : ℝ) < x := by linarith
  have hbose_pos : 0 < boseKernel x := by
    rw [boseKernel]
    have h1 : Real.exp (-x) < 1 := by
      rw [Real.exp_lt_one_iff]
      linarith
    have h2 : 0 < 1 - Real.exp (-x) := by linarith
    positivity
  have hbose_le : boseKernel x ≤ 4 * Real.exp (-x) := by
    rw [boseKernel]
    have hexp1 : Real.exp (-x) ≤ Real.exp (-1) := by
      apply Real.exp_le_exp.mpr
      linarith
    have he1 : Real.exp (-1) ≤ 1 / 2 := by
      have h2e : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
      have hprod : Real.exp (-1) * Real.exp 1 = 1 := by
        rw [← Real.exp_add]
        norm_num
      nlinarith [Real.exp_pos (-1),
        mul_le_mul_of_nonneg_left h2e (Real.exp_pos (-1)).le]
    have hden : (1 : ℝ) / 2 ≤ 1 - Real.exp (-x) := by linarith
    have hden_sq : (1 : ℝ) / 4 ≤ (1 - Real.exp (-x)) ^ 2 := by nlinarith
    rw [div_le_iff₀ (by nlinarith : (0:ℝ) < (1 - Real.exp (-x)) ^ 2)]
    nlinarith [Real.exp_pos (-x)]
  have hsplit : |boseReg0 x| ≤ boseKernel x + 1 / x ^ 2 := by
    rw [boseReg0]
    calc |boseKernel x - 1 / x ^ 2|
        ≤ |boseKernel x| + |1 / x ^ 2| := abs_sub _ _
      _ = boseKernel x + 1 / x ^ 2 := by
          rw [abs_of_pos hbose_pos, abs_of_pos (by positivity : (0:ℝ) < 1 / x ^ 2)]
  linarith

end AnalyticCombinatorics.Ch8.Partitions.Erdos
