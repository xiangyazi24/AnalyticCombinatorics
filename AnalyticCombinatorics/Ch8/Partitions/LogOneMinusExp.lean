import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Ch8 §VIII — The function `-log(1 - e^{-x})` (toward the HR constant)

Building block for the second-order partition-product asymptotic (DOCTRINE
avenue d, brick 2): `P(e^{-t}) ~ √(t/2π)·e^{A/t}`.  This file isolates the
summand `f(x) = -log(1 - e^{-x})` and its log-regularized form
`h(x) = f(x) + log x`, which removes the logarithmic singularity at `0`
(`h(x) → 0` as `x → 0+`).

These feed the singular Euler–Maclaurin split
`∑_k f(kt) = ∑_k -log(tk) + ∑_k h(kt) + tail` in `ProductSecondOrder.lean`,
where the `√(2π)` constant ultimately comes from Mathlib's Stirling theorem.
-/

namespace AnalyticCombinatorics.Ch8.Partitions

open Real Filter Topology

/-- `f(x) = -log(1 - e^{-x})`, the Euler-product log summand. -/
noncomputable def log1mexp (x : ℝ) : ℝ := -Real.log (1 - Real.exp (-x))

/-- `h(x) = -log(1 - e^{-x}) + log x`, the log-regularized summand: it removes
the `-log x` singularity of `log1mexp` at `0`, so `h(x) → 0` as `x → 0+`. -/
noncomputable def log1mexpReg (x : ℝ) : ℝ := log1mexp x + Real.log x

/-- For `x > 0`, `1 - e^{-x} > 0`. -/
lemma one_sub_exp_neg_pos {x : ℝ} (hx : 0 < x) : 0 < 1 - Real.exp (-x) := by
  have : Real.exp (-x) < 1 := by
    rw [Real.exp_lt_one_iff]; linarith
  linarith

/-- `log1mexp` is nonnegative for `x > 0` (since `0 < 1 - e^{-x} ≤ 1`). -/
lemma log1mexp_nonneg {x : ℝ} (hx : 0 < x) : 0 ≤ log1mexp x := by
  unfold log1mexp
  have h1 : 1 - Real.exp (-x) ≤ 1 := by
    have : 0 < Real.exp (-x) := Real.exp_pos _
    linarith
  have := Real.log_nonpos (le_of_lt (one_sub_exp_neg_pos hx)) h1
  linarith

/-- Regularized form as a single logarithm: `h(x) = -log((1 - e^{-x})/x)`. -/
lemma log1mexpReg_eq {x : ℝ} (hx : 0 < x) :
    log1mexpReg x = -Real.log ((1 - Real.exp (-x)) / x) := by
  have h1 : 0 < 1 - Real.exp (-x) := one_sub_exp_neg_pos hx
  unfold log1mexpReg log1mexp
  rw [Real.log_div (ne_of_gt h1) (ne_of_gt hx)]
  ring

/-- Tail bound: for `x ≥ log 2`, `|log1mexp x| ≤ 2 e^{-x}` (exponential decay).
Uses `-log(1-y) ≤ y/(1-y) ≤ 2y` for `y = e^{-x} ≤ 1/2`. -/
lemma log1mexp_tail_bound {x : ℝ} (hx : Real.log 2 ≤ x) :
    |log1mexp x| ≤ 2 * Real.exp (-x) := by
  have hx0 : 0 < x := lt_of_lt_of_le (Real.log_pos (by norm_num)) hx
  have hle : Real.exp (-x) ≤ 1 / 2 := by
    have hval : Real.exp (-Real.log 2) = 1 / 2 := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 2)]; norm_num
    have h2 : Real.exp (-x) ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.mpr (by linarith)
    rwa [hval] at h2
  have hy0 : 0 < Real.exp (-x) := Real.exp_pos _
  have h1 : 0 < 1 - Real.exp (-x) := one_sub_exp_neg_pos hx0
  rw [abs_of_nonneg (log1mexp_nonneg hx0)]
  unfold log1mexp
  set y := Real.exp (-x) with hy
  -- Mathlib lower bound: 1 - (1-y)⁻¹ ≤ log(1-y), hence -log(1-y) ≤ (1-y)⁻¹ - 1.
  have hlb : 1 - (1 - y)⁻¹ ≤ Real.log (1 - y) := Real.one_sub_inv_le_log_of_pos h1
  -- eliminate the inverse via w·(1-y) = 1, then (1-y)⁻¹ - 1 ≤ 2y for y ≤ 1/2.
  have hw : (1 - y)⁻¹ * (1 - y) = 1 := inv_mul_cancel₀ (ne_of_gt h1)
  have hwpos : 0 < (1 - y)⁻¹ := inv_pos.mpr h1
  nlinarith [hlb, hw, hwpos, hy0, hle, h1,
    mul_nonneg hy0.le (show (0:ℝ) ≤ 1 - 2 * y by linarith)]

/-- Derivative of `f(x) = -log(1 - e^{-x})` for `x > 0`:
`f'(x) = -e^{-x}/(1 - e^{-x}) = -1/(e^x - 1)`. -/
lemma log1mexp_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt log1mexp (-Real.exp (-x) / (1 - Real.exp (-x))) x := by
  have hpos : 0 < 1 - Real.exp (-x) := one_sub_exp_neg_pos hx
  have hin : HasDerivAt (fun x : ℝ => 1 - Real.exp (-x)) (Real.exp (-x)) x := by
    have h1 : HasDerivAt (fun x : ℝ => Real.exp (-x)) (-Real.exp (-x)) x := by
      have := (Real.hasDerivAt_exp (-x)).comp x ((hasDerivAt_id x).neg)
      simpa using this
    simpa using (hasDerivAt_const x (1 : ℝ)).sub h1
  have hout : HasDerivAt (fun y : ℝ => -Real.log y)
      (-(1 - Real.exp (-x))⁻¹) (1 - Real.exp (-x)) :=
    (Real.hasDerivAt_log (ne_of_gt hpos)).neg
  have hcomp := hout.comp x hin
  simpa [log1mexp, div_eq_mul_inv, mul_comm] using hcomp

/-- The regularized summand vanishes at the singularity: `h(x) → 0` as `x → 0+`.
Proof: `h(x) = -log((1 - e^{-x})/x)` and `(1 - e^{-x})/x → 1` (slope of
`x ↦ 1 - e^{-x}` at `0`), so `h(x) → -log 1 = 0`. -/
lemma log1mexpReg_tendsto_zero :
    Tendsto log1mexpReg (𝓝[>] 0) (𝓝 0) := by
  have h1 : HasDerivAt (fun x : ℝ => Real.exp (-x)) (-1) 0 := by
    have := (Real.hasDerivAt_exp (-0 : ℝ)).comp (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).neg)
    simpa using this
  have hd : HasDerivAt (fun x : ℝ => 1 - Real.exp (-x)) 1 0 := by
    simpa using (hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub h1
  have hslope : Tendsto (slope (fun x : ℝ => 1 - Real.exp (-x)) 0) (𝓝[≠] 0) (𝓝 1) :=
    hasDerivAt_iff_tendsto_slope.mp hd
  have hratio : Tendsto (fun b : ℝ => (1 - Real.exp (-b)) / b) (𝓝[≠] 0) (𝓝 1) :=
    Filter.Tendsto.congr (fun b => by rw [slope_def_field]; simp [Real.exp_zero]) hslope
  have hsub : (𝓝[>] (0 : ℝ)) ≤ 𝓝[≠] (0 : ℝ) := nhdsWithin_mono 0 (fun y hy => ne_of_gt hy)
  have hc : Tendsto (fun y : ℝ => Real.log y) (𝓝 1) (𝓝 0) := by
    have := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto
    simpa using this
  have hlog : Tendsto (fun x : ℝ => -Real.log ((1 - Real.exp (-x)) / x)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (hc.comp (hratio.mono_left hsub)).neg
  refine hlog.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (log1mexpReg_eq hx).symm

end AnalyticCombinatorics.Ch8.Partitions
