import AnalyticCombinatorics.Ch8.Partitions.TailCell

/-!
# `log1mexp` per-cell tail bound (HR constant, brick 2 tail)

`log1mexp'(x) = -1/(e^x-1)` is `4e^{-a}`-Lipschitz on a tail cell `[a,a+h]` (a ≥ log 2),
via FTC on its derivative `e^x/(e^x-1)²` (bounded `≤ 4e^{-x}`). Hence the per-cell
trapezoid error is `≤ 4 e^{-a} h²` (apply `cell_trapezoid_bound_of_local_lipschitz_deriv`).
-/

namespace AnalyticCombinatorics.Ch8.Partitions

open Filter Topology MeasureTheory Real
open scoped Topology Interval

noncomputable section

/-- `log1mexp'` is `4e^{-a}`-Lipschitz on a tail cell `[a,a+h]` (`a ≥ log 2`). -/
lemma log1mexp_deriv_lipschitz_tail_cell {a h : ℝ} (ha : Real.log 2 ≤ a) :
    ∀ z ∈ Set.Icc a (a + h), ∀ w ∈ Set.Icc a (a + h),
      |-(1 / (Real.exp z - 1)) - -(1 / (Real.exp w - 1))| ≤ (4 * Real.exp (-a)) * |z - w| := by
  intro z hz w hw
  have hge : ∀ x ∈ Set.uIcc z w, a ≤ x := by
    intro x hx
    rcases Set.mem_uIcc.mp hx with h | h
    · exact le_trans hz.1 h.1
    · exact le_trans hw.1 h.1
  have hxpos : ∀ x ∈ Set.uIcc z w, 0 < x := fun x hx =>
    lt_of_lt_of_le (Real.log_pos (by norm_num : (1 : ℝ) < 2)) (le_trans ha (hge x hx))
  have hderiv : ∀ x ∈ Set.uIcc z w,
      HasDerivAt (fun y : ℝ => -(1 / (Real.exp y - 1))) (Real.exp x / (Real.exp x - 1) ^ 2) x :=
    fun x hx => log1mexpDeriv_hasDerivAt (hxpos x hx)
  have hcont : ContinuousOn (fun x : ℝ => Real.exp x / (Real.exp x - 1) ^ 2) (Set.uIcc z w) := by
    intro x hx
    have hden : (Real.exp x - 1) ^ 2 ≠ 0 := by
      have : 0 < Real.exp x - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr (hxpos x hx)); positivity
    exact ((Real.continuous_exp.continuousAt).div
      (((Real.continuous_exp.sub continuous_const).pow 2).continuousAt) hden).continuousWithinAt
  have hint : IntervalIntegrable (fun x : ℝ => Real.exp x / (Real.exp x - 1) ^ 2)
      MeasureTheory.volume z w := hcont.intervalIntegrable
  have hFTC : (∫ x in z..w, Real.exp x / (Real.exp x - 1) ^ 2)
      = (-(1 / (Real.exp w - 1))) - (-(1 / (Real.exp z - 1))) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hpoint : ∀ x ∈ Set.uIoc z w, ‖Real.exp x / (Real.exp x - 1) ^ 2‖ ≤ 4 * Real.exp (-a) := by
    intro x hx
    have hxge : a ≤ x := hge x (Set.Ioc_subset_Icc_self hx)
    rw [Real.norm_eq_abs]
    calc |Real.exp x / (Real.exp x - 1) ^ 2| ≤ 4 * Real.exp (-x) :=
          log1mexp_second_deriv_tail_bound (le_trans ha hxge)
      _ ≤ 4 * Real.exp (-a) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)
  have hnorm : ‖∫ x in z..w, Real.exp x / (Real.exp x - 1) ^ 2‖ ≤ (4 * Real.exp (-a)) * |w - z| :=
    intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  calc |-(1 / (Real.exp z - 1)) - -(1 / (Real.exp w - 1))|
        = ‖∫ x in z..w, Real.exp x / (Real.exp x - 1) ^ 2‖ := by
          rw [hFTC, Real.norm_eq_abs, abs_sub_comm]
    _ ≤ (4 * Real.exp (-a)) * |w - z| := hnorm
    _ = (4 * Real.exp (-a)) * |z - w| := by rw [abs_sub_comm]

/-- Per-cell tail trapezoid bound for `log1mexp`: `≤ 4 e^{-a} h²`. -/
lemma log1mexp_tail_cell_bound {a h : ℝ} (hh : 0 < h) (ha : Real.log 2 ≤ a) :
    |((log1mexp a + log1mexp (a + h)) / 2) - (1 / h) * ∫ x in a..(a + h), log1mexp x|
      ≤ (4 * Real.exp (-a)) * h ^ 2 := by
  have hderiv : ∀ x ∈ Set.Icc a (a + h), HasDerivAt log1mexp (-(1 / (Real.exp x - 1))) x :=
    fun x hx => log1mexp_hasDerivAt_tail
      (lt_of_lt_of_le (Real.log_pos (by norm_num : (1 : ℝ) < 2)) (le_trans ha hx.1))
  have hint_g : IntervalIntegrable log1mexp MeasureTheory.volume a (a + h) := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le (by linarith : a ≤ a + h)] at hx
    exact (log1mexp_hasDerivAt_tail
      (lt_of_lt_of_le (Real.log_pos (by norm_num : (1 : ℝ) < 2)) (le_trans ha hx.1))).continuousAt.continuousWithinAt
  have hint_gp : IntervalIntegrable (fun x : ℝ => -(1 / (Real.exp x - 1)))
      MeasureTheory.volume a (a + h) := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le (by linarith : a ≤ a + h)] at hx
    have hxpos : 0 < x := lt_of_lt_of_le (Real.log_pos (by norm_num : (1 : ℝ) < 2)) (le_trans ha hx.1)
    have hden : Real.exp x - 1 ≠ 0 := sub_ne_zero.mpr (Real.one_lt_exp_iff.mpr hxpos).ne'
    exact ((continuousAt_const.div
      (Real.continuous_exp.continuousAt.sub continuousAt_const) hden).neg).continuousWithinAt
  exact cell_trapezoid_bound_of_local_lipschitz_deriv (by positivity) hh hderiv hint_g hint_gp
    (log1mexp_deriv_lipschitz_tail_cell ha)

end

end AnalyticCombinatorics.Ch8.Partitions
