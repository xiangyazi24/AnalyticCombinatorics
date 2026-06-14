import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.LogOneMinusExpTail

/-!
# Local-domain per-cell trapezoid bound (HR constant, brick 2 tail)

Per-cell trapezoid error `≤ L·h²` from a Lipschitz derivative on the cell `[a,a+h]`
itself (local-domain version of `TrapezoidCellIoc`, chord-interpolation proof).
Then the concrete `log1mexp` tail cell bound `≤ 4 e^{-a} h²` (ChatGPT R8 route).
-/

namespace AnalyticCombinatorics.Ch8.Partitions

open Filter Topology MeasureTheory Real
open scoped Topology Interval

noncomputable section

/-- Chord through `(a,g a)`, `(a+h,g(a+h))`. -/
private noncomputable def chordT (g : ℝ → ℝ) (a h x : ℝ) : ℝ :=
  ((g (a + h) - g a) / h) * x + (((a + h) * g a - a * g (a + h)) / h)

private lemma chordT_eq_endpoint (g : ℝ → ℝ) {a h x : ℝ} (hh : h ≠ 0) :
    chordT g a h x = ((a + h - x) / h) * g a + ((x - a) / h) * g (a + h) := by
  unfold chordT; field_simp [hh]; ring

private lemma integral_chordT (g : ℝ → ℝ) {a h : ℝ} (hh : h ≠ 0) :
    (∫ x in a..(a + h), chordT g a h x) = h * ((g a + g (a + h)) / 2) := by
  unfold chordT
  set A : ℝ := (g (a + h) - g a) / h with hA
  set B : ℝ := ((a + h) * g a - a * g (a + h)) / h with hB
  have hInt1 : IntervalIntegrable (fun x : ℝ => A * x) MeasureTheory.volume a (a + h) :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  have hInt2 : IntervalIntegrable (fun _x : ℝ => B) MeasureTheory.volume a (a + h) :=
    continuous_const.intervalIntegrable _ _
  change (∫ x in a..(a + h), A * x + B) = h * ((g a + g (a + h)) / 2)
  rw [intervalIntegral.integral_add hInt1 hInt2, intervalIntegral.integral_const_mul,
    integral_id, intervalIntegral.integral_const]
  rw [hA, hB]; simp only [smul_eq_mul]; field_simp [hh]; ring

private lemma first_order_error_local
    {g gp : ℝ → ℝ} {L a h x y : ℝ} (hL : 0 ≤ L)
    (hxI : x ∈ Set.Icc a (a + h)) (hyI : y ∈ Set.Icc a (a + h))
    (hderiv : ∀ z ∈ Set.Icc a (a + h), HasDerivAt g (gp z) z)
    (hint_gp : IntervalIntegrable gp MeasureTheory.volume a (a + h))
    (hlip : ∀ z ∈ Set.Icc a (a + h), ∀ w ∈ Set.Icc a (a + h), |gp z - gp w| ≤ L * |z - w|) :
    |g y - g x - (y - x) * gp x| ≤ L * (y - x) ^ 2 := by
  have hsub : Set.uIcc x y ⊆ Set.Icc a (a + h) := Set.uIcc_subset_Icc hxI hyI
  have hIntGp : IntervalIntegrable gp MeasureTheory.volume x y :=
    hint_gp.mono_set (by rw [Set.uIcc_of_le (le_trans hxI.1 hxI.2)]; exact hsub)
  have hIntConst : IntervalIntegrable (fun _z : ℝ => gp x) MeasureTheory.volume x y :=
    continuous_const.intervalIntegrable _ _
  have hIntDiff : IntervalIntegrable (fun z : ℝ => gp z - gp x) MeasureTheory.volume x y :=
    hIntGp.sub hIntConst
  have hderivF : ∀ z ∈ Set.uIcc x y,
      HasDerivAt (fun z : ℝ => g z - z * gp x) (gp z - gp x) z := by
    intro z hz
    have hg := hderiv z (hsub hz)
    have hlin : HasDerivAt (fun z : ℝ => z * gp x) (gp x) z := by
      simpa using (hasDerivAt_id z).mul_const (gp x)
    exact hg.sub hlin
  have hFTC : (∫ z in x..y, gp z - gp x) = (g y - y * gp x) - (g x - x * gp x) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderivF hIntDiff
  have herr_eq : g y - g x - (y - x) * gp x = ∫ z in x..y, gp z - gp x := by rw [hFTC]; ring
  have hnorm : ‖∫ z in x..y, gp z - gp x‖ ≤ (L * |y - x|) * |y - x| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
    intro z hz
    have hzmem : z ∈ Set.uIcc x y := Set.Ioc_subset_Icc_self hz
    have hzI : z ∈ Set.Icc a (a + h) := hsub hzmem
    have hzx : |z - x| ≤ |y - x| := by
      rcases le_total x y with hle | hle
      · rw [Set.uIoc_of_le hle] at hz
        rw [abs_of_nonneg (by linarith [hz.1] : (0:ℝ) ≤ z - x),
          abs_of_nonneg (by linarith : (0:ℝ) ≤ y - x)]; linarith [hz.2]
      · rw [Set.uIoc_comm, Set.uIoc_of_le hle] at hz
        rw [abs_of_nonpos (by linarith [hz.2] : z - x ≤ 0),
          abs_of_nonpos (by linarith : y - x ≤ 0)]; linarith [hz.1]
    rw [Real.norm_eq_abs]
    calc |gp z - gp x| ≤ L * |z - x| := hlip z hzI x hxI
      _ ≤ L * |y - x| := mul_le_mul_of_nonneg_left hzx hL
  calc |g y - g x - (y - x) * gp x| = ‖∫ z in x..y, gp z - gp x‖ := by
        rw [herr_eq, Real.norm_eq_abs]
    _ ≤ (L * |y - x|) * |y - x| := hnorm
    _ = L * (y - x) ^ 2 := by rw [mul_assoc, abs_mul_abs_self]; ring

private lemma chordT_error_bound
    {g gp : ℝ → ℝ} {L a h x : ℝ} (hL : 0 ≤ L) (hh : 0 < h)
    (hderiv : ∀ z ∈ Set.Icc a (a + h), HasDerivAt g (gp z) z)
    (hint_gp : IntervalIntegrable gp MeasureTheory.volume a (a + h))
    (hlip : ∀ z ∈ Set.Icc a (a + h), ∀ w ∈ Set.Icc a (a + h), |gp z - gp w| ≤ L * |z - w|)
    (hx : x ∈ Set.Icc a (a + h)) :
    |chordT g a h x - g x| ≤ L * h ^ 2 := by
  have hxa : a ≤ x := hx.1
  have hxb : x ≤ a + h := hx.2
  have haI : a ∈ Set.Icc a (a + h) := ⟨le_rfl, by linarith⟩
  have habI : a + h ∈ Set.Icc a (a + h) := ⟨by linarith, le_rfl⟩
  have e1 : |g x - g a - (x - a) * gp x| ≤ L * (x - a) ^ 2 := by
    have hfo := first_order_error_local (g := g) (gp := gp) (L := L) (x := x) (y := a)
      hL hx haI hderiv hint_gp hlip
    rw [show g x - g a - (x - a) * gp x = -(g a - g x - (a - x) * gp x) by ring, abs_neg,
      show (x - a) ^ 2 = (a - x) ^ 2 by ring]
    exact hfo
  have e2 : |g (a + h) - g x - (a + h - x) * gp x| ≤ L * (a + h - x) ^ 2 :=
    first_order_error_local (g := g) (gp := gp) (L := L) (x := x) (y := a + h)
      hL hx habI hderiv hint_gp hlip
  have hα : 0 ≤ x - a := sub_nonneg.mpr hxa
  have hβ : 0 ≤ a + h - x := sub_nonneg.mpr hxb
  have hαh : 0 ≤ (x - a) / h := div_nonneg hα hh.le
  have hβh : 0 ≤ (a + h - x) / h := div_nonneg hβ hh.le
  have herr : g x - chordT g a h x =
      ((a + h - x) / h) * (g x - g a - (x - a) * gp x)
        - ((x - a) / h) * (g (a + h) - g x - (a + h - x) * gp x) := by
    rw [chordT_eq_endpoint g hh.ne']; field_simp [hh.ne']; ring
  have hterm1 : |((a + h - x) / h) * (g x - g a - (x - a) * gp x)|
        ≤ ((a + h - x) / h) * (L * (x - a) ^ 2) := by
    rw [abs_mul, abs_of_nonneg hβh]; exact mul_le_mul_of_nonneg_left e1 hβh
  have hterm2 : |((x - a) / h) * (g (a + h) - g x - (a + h - x) * gp x)|
        ≤ ((x - a) / h) * (L * (a + h - x) ^ 2) := by
    rw [abs_mul, abs_of_nonneg hαh]; exact mul_le_mul_of_nonneg_left e2 hαh
  have hmain : |g x - chordT g a h x| ≤ L * (x - a) * (a + h - x) := by
    rw [herr]
    calc |((a + h - x) / h) * (g x - g a - (x - a) * gp x)
            - ((x - a) / h) * (g (a + h) - g x - (a + h - x) * gp x)|
          ≤ |((a + h - x) / h) * (g x - g a - (x - a) * gp x)|
            + |((x - a) / h) * (g (a + h) - g x - (a + h - x) * gp x)| := abs_sub _ _
      _ ≤ ((a + h - x) / h) * (L * (x - a) ^ 2)
            + ((x - a) / h) * (L * (a + h - x) ^ 2) := add_le_add hterm1 hterm2
      _ = L * (x - a) * (a + h - x) := by field_simp [hh.ne']; ring
  rw [abs_sub_comm]
  calc |g x - chordT g a h x| ≤ L * (x - a) * (a + h - x) := hmain
    _ ≤ L * h ^ 2 := by
        have hαle : x - a ≤ h := by linarith
        have hβle : a + h - x ≤ h := by linarith
        nlinarith [hL, hα, hβ, hαle, hβle]

/-- Per-cell trapezoid bound from a Lipschitz derivative on the cell `[a,a+h]`. -/
theorem cell_trapezoid_bound_of_local_lipschitz_deriv
    {g gp : ℝ → ℝ} {L a h : ℝ} (hL : 0 ≤ L) (hh : 0 < h)
    (hderiv : ∀ x ∈ Set.Icc a (a + h), HasDerivAt g (gp x) x)
    (hint_g : IntervalIntegrable g MeasureTheory.volume a (a + h))
    (hint_gp : IntervalIntegrable gp MeasureTheory.volume a (a + h))
    (hlip : ∀ z ∈ Set.Icc a (a + h), ∀ w ∈ Set.Icc a (a + h), |gp z - gp w| ≤ L * |z - w|) :
    |((g a + g (a + h)) / 2) - (1 / h) * ∫ x in a..(a + h), g x| ≤ L * h ^ 2 := by
  have hChordInt : (∫ x in a..(a + h), chordT g a h x) = h * ((g a + g (a + h)) / 2) :=
    integral_chordT g hh.ne'
  have hIntChord : IntervalIntegrable (fun x : ℝ => chordT g a h x)
      MeasureTheory.volume a (a + h) := by
    unfold chordT
    exact ((continuous_const.mul continuous_id).add continuous_const).intervalIntegrable _ _
  have hsubInt : (∫ x in a..(a + h), chordT g a h x - g x)
      = (∫ x in a..(a + h), chordT g a h x) - ∫ x in a..(a + h), g x :=
    intervalIntegral.integral_sub hIntChord hint_g
  have herr_eq : ((g a + g (a + h)) / 2) - (1 / h) * ∫ x in a..(a + h), g x
      = (1 / h) * ∫ x in a..(a + h), chordT g a h x - g x := by
    rw [hsubInt, hChordInt]; field_simp [hh.ne']
  have hpoint : ∀ x ∈ Set.uIoc a (a + h), ‖chordT g a h x - g x‖ ≤ L * h ^ 2 := by
    intro x hx
    have hxIoc : x ∈ Set.Ioc a (a + h) := by
      simpa [Set.uIoc_of_le (by linarith : a ≤ a + h)] using hx
    have hxIcc : x ∈ Set.Icc a (a + h) := ⟨le_of_lt hxIoc.1, hxIoc.2⟩
    rw [Real.norm_eq_abs]
    exact chordT_error_bound (g := g) (gp := gp) (L := L) hL hh hderiv hint_gp hlip hxIcc
  have hnorm : ‖∫ x in a..(a + h), chordT g a h x - g x‖ ≤ (L * h ^ 2) * |(a + h) - a| :=
    intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  calc |((g a + g (a + h)) / 2) - (1 / h) * ∫ x in a..(a + h), g x|
        = |(1 / h) * ∫ x in a..(a + h), chordT g a h x - g x| := by rw [herr_eq]
    _ = (1 / h) * ‖∫ x in a..(a + h), chordT g a h x - g x‖ := by
        rw [abs_mul, abs_of_pos (one_div_pos.mpr hh), ← Real.norm_eq_abs]
    _ ≤ (1 / h) * ((L * h ^ 2) * |(a + h) - a|) := mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = L * h ^ 2 := by rw [show (a + h) - a = h by ring, abs_of_pos hh]; field_simp [hh.ne']

end

end AnalyticCombinatorics.Ch8.Partitions
