import Mathlib

/-!
# Per-cell trapezoid error from a Lipschitz derivative — open-left `(0,2]` version

Variant of `TrapezoidCell.lean`'s producer with hypotheses on `Set.Ioc 0 2`
(derivative need not exist at `0`), for functions like `log1mexpReg` whose
derivative is only defined on `(0,∞)`.  Cells `[a,a+h]` require `0 < a`.
-/

namespace AnalyticCombinatorics.Ch8.Partitions

open Filter Topology BigOperators
open scoped Topology BigOperators Interval

noncomputable section

private noncomputable def chordI (g : ℝ → ℝ) (a h x : ℝ) : ℝ :=
  ((g (a + h) - g a) / h) * x + (((a + h) * g a - a * g (a + h)) / h)

private lemma chordI_eq_endpoint (g : ℝ → ℝ) {a h x : ℝ} (hh : h ≠ 0) :
    chordI g a h x = ((a + h - x) / h) * g a + ((x - a) / h) * g (a + h) := by
  unfold chordI; field_simp [hh]; ring

private lemma integral_chordI (g : ℝ → ℝ) {a h : ℝ} (hh : h ≠ 0) :
    (∫ x in a..(a + h), chordI g a h x) = h * ((g a + g (a + h)) / 2) := by
  unfold chordI
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

/-- `uIcc x y ⊆ Ioc 0 2` when `x, y ∈ Ioc 0 2`. -/
private lemma uIcc_subset_Ioc02 {x y : ℝ}
    (hxI : x ∈ Set.Ioc (0 : ℝ) 2) (hyI : y ∈ Set.Ioc (0 : ℝ) 2) :
    Set.uIcc x y ⊆ Set.Ioc (0 : ℝ) 2 := by
  intro z hz
  rcases Set.mem_uIcc.mp hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨lt_of_lt_of_le hxI.1 h1, le_trans h2 hyI.2⟩
  · exact ⟨lt_of_lt_of_le hyI.1 h1, le_trans h2 hxI.2⟩

private lemma first_order_error_Ioc
    {g gp : ℝ → ℝ} {M x y : ℝ} (hM : 0 ≤ M)
    (hxI : x ∈ Set.Ioc (0 : ℝ) 2) (hyI : y ∈ Set.Ioc (0 : ℝ) 2)
    (hderiv : ∀ z ∈ Set.Ioc (0 : ℝ) 2, HasDerivAt g (gp z) z)
    (hint_gp : ∀ ⦃u v : ℝ⦄, 0 < u → u ≤ v → v ≤ 2 →
        IntervalIntegrable gp MeasureTheory.volume u v)
    (hlip : ∀ z ∈ Set.Ioc (0 : ℝ) 2, ∀ w ∈ Set.Ioc (0 : ℝ) 2,
        |gp z - gp w| ≤ M * |z - w|) :
    |g y - g x - (y - x) * gp x| ≤ M * (y - x) ^ 2 := by
  have hsub : Set.uIcc x y ⊆ Set.Ioc (0 : ℝ) 2 := uIcc_subset_Ioc02 hxI hyI
  have hIntGp : IntervalIntegrable gp MeasureTheory.volume x y := by
    rcases le_total x y with hle | hle
    · exact hint_gp hxI.1 hle hyI.2
    · exact (hint_gp hyI.1 hle hxI.2).symm
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
  have hnorm : ‖∫ z in x..y, gp z - gp x‖ ≤ (M * |y - x|) * |y - x| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
    intro z hz
    have hzx : |z - x| ≤ |y - x| ∧ z ∈ Set.Ioc (0 : ℝ) 2 := by
      rcases le_total x y with hle | hle
      · rw [Set.uIoc_of_le hle] at hz
        refine ⟨?_, lt_of_lt_of_le hxI.1 (le_of_lt hz.1), le_trans hz.2 hyI.2⟩
        rw [abs_of_nonneg (by linarith [hz.1] : (0:ℝ) ≤ z - x),
          abs_of_nonneg (by linarith : (0:ℝ) ≤ y - x)]; linarith [hz.2]
      · rw [Set.uIoc_comm, Set.uIoc_of_le hle] at hz
        refine ⟨?_, lt_of_lt_of_le hyI.1 (le_of_lt hz.1), le_trans hz.2 hxI.2⟩
        rw [abs_of_nonpos (by linarith [hz.2] : z - x ≤ 0),
          abs_of_nonpos (by linarith : y - x ≤ 0)]; linarith [hz.1]
    rw [Real.norm_eq_abs]
    calc |gp z - gp x| ≤ M * |z - x| := hlip z hzx.2 x hxI
      _ ≤ M * |y - x| := mul_le_mul_of_nonneg_left hzx.1 hM
  calc |g y - g x - (y - x) * gp x| = ‖∫ z in x..y, gp z - gp x‖ := by
        rw [herr_eq, Real.norm_eq_abs]
    _ ≤ (M * |y - x|) * |y - x| := hnorm
    _ = M * (y - x) ^ 2 := by rw [mul_assoc, abs_mul_abs_self]; ring

private lemma chordI_error_bound
    {g gp : ℝ → ℝ} {M a h x : ℝ} (hM : 0 ≤ M)
    (hh : 0 < h) (ha : 0 < a) (hb : a + h ≤ 2)
    (hderiv : ∀ z ∈ Set.Ioc (0 : ℝ) 2, HasDerivAt g (gp z) z)
    (hint_gp : ∀ ⦃u v : ℝ⦄, 0 < u → u ≤ v → v ≤ 2 →
        IntervalIntegrable gp MeasureTheory.volume u v)
    (hlip : ∀ z ∈ Set.Ioc (0 : ℝ) 2, ∀ w ∈ Set.Ioc (0 : ℝ) 2,
        |gp z - gp w| ≤ M * |z - w|)
    (hx : x ∈ Set.Icc a (a + h)) :
    |chordI g a h x - g x| ≤ M * h ^ 2 := by
  have hxa : a ≤ x := hx.1
  have hxb : x ≤ a + h := hx.2
  have hx0 : 0 < x := lt_of_lt_of_le ha hxa
  have hx2 : x ≤ 2 := le_trans hxb hb
  have hxI : x ∈ Set.Ioc (0 : ℝ) 2 := ⟨hx0, hx2⟩
  have haI : a ∈ Set.Ioc (0 : ℝ) 2 := ⟨ha, by linarith⟩
  have habI : a + h ∈ Set.Ioc (0 : ℝ) 2 := ⟨by linarith, hb⟩
  have e1 : |g x - g a - (x - a) * gp x| ≤ M * (x - a) ^ 2 := by
    have hfo := first_order_error_Ioc (g := g) (gp := gp) (M := M)
      (x := x) (y := a) hM hxI haI hderiv hint_gp hlip
    rw [show g x - g a - (x - a) * gp x = -(g a - g x - (a - x) * gp x) by ring, abs_neg,
      show (x - a) ^ 2 = (a - x) ^ 2 by ring]
    exact hfo
  have e2 : |g (a + h) - g x - (a + h - x) * gp x| ≤ M * (a + h - x) ^ 2 :=
    first_order_error_Ioc (g := g) (gp := gp) (M := M) (x := x) (y := a + h)
      hM hxI habI hderiv hint_gp hlip
  have hα : 0 ≤ x - a := sub_nonneg.mpr hxa
  have hβ : 0 ≤ a + h - x := sub_nonneg.mpr hxb
  have hαh : 0 ≤ (x - a) / h := div_nonneg hα hh.le
  have hβh : 0 ≤ (a + h - x) / h := div_nonneg hβ hh.le
  have herr : g x - chordI g a h x =
      ((a + h - x) / h) * (g x - g a - (x - a) * gp x)
        - ((x - a) / h) * (g (a + h) - g x - (a + h - x) * gp x) := by
    rw [chordI_eq_endpoint g hh.ne']; field_simp [hh.ne']; ring
  have hterm1 : |((a + h - x) / h) * (g x - g a - (x - a) * gp x)|
        ≤ ((a + h - x) / h) * (M * (x - a) ^ 2) := by
    rw [abs_mul, abs_of_nonneg hβh]; exact mul_le_mul_of_nonneg_left e1 hβh
  have hterm2 : |((x - a) / h) * (g (a + h) - g x - (a + h - x) * gp x)|
        ≤ ((x - a) / h) * (M * (a + h - x) ^ 2) := by
    rw [abs_mul, abs_of_nonneg hαh]; exact mul_le_mul_of_nonneg_left e2 hαh
  have hmain : |g x - chordI g a h x| ≤ M * (x - a) * (a + h - x) := by
    rw [herr]
    calc |((a + h - x) / h) * (g x - g a - (x - a) * gp x)
            - ((x - a) / h) * (g (a + h) - g x - (a + h - x) * gp x)|
          ≤ |((a + h - x) / h) * (g x - g a - (x - a) * gp x)|
            + |((x - a) / h) * (g (a + h) - g x - (a + h - x) * gp x)| := abs_sub _ _
      _ ≤ ((a + h - x) / h) * (M * (x - a) ^ 2)
            + ((x - a) / h) * (M * (a + h - x) ^ 2) := add_le_add hterm1 hterm2
      _ = M * (x - a) * (a + h - x) := by field_simp [hh.ne']; ring
  rw [abs_sub_comm]
  calc |g x - chordI g a h x| ≤ M * (x - a) * (a + h - x) := hmain
    _ ≤ M * h ^ 2 := by
        have hαle : x - a ≤ h := by linarith
        have hβle : a + h - x ≤ h := by linarith
        nlinarith [hM, hα, hβ, hαle, hβle]

/-- Per-cell trapezoid producer, open-left version (cells `[a,a+h]` with `a>0`). -/
theorem cell_trapezoid_bound_of_lipschitz_deriv_Ioc
    {g gp : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hderiv : ∀ z ∈ Set.Ioc (0 : ℝ) 2, HasDerivAt g (gp z) z)
    (hint_g : ∀ ⦃u v : ℝ⦄, 0 < u → u ≤ v → v ≤ 2 →
        IntervalIntegrable g MeasureTheory.volume u v)
    (hint_gp : ∀ ⦃u v : ℝ⦄, 0 < u → u ≤ v → v ≤ 2 →
        IntervalIntegrable gp MeasureTheory.volume u v)
    (hlip : ∀ z ∈ Set.Ioc (0 : ℝ) 2, ∀ w ∈ Set.Ioc (0 : ℝ) 2,
        |gp z - gp w| ≤ M * |z - w|) :
    ∀ ⦃a h : ℝ⦄, 0 < h → 0 < a → a + h ≤ 2 →
        |((g a + g (a + h)) / 2) - (1 / h) * ∫ x in a..(a + h), g x| ≤ M * h ^ 2 := by
  intro a h hh ha hb
  have hIntG : IntervalIntegrable g MeasureTheory.volume a (a + h) :=
    hint_g ha (by linarith) hb
  have hIntChord : IntervalIntegrable (fun x : ℝ => chordI g a h x)
      MeasureTheory.volume a (a + h) := by
    unfold chordI
    exact ((continuous_const.mul continuous_id).add continuous_const).intervalIntegrable _ _
  have hChordInt : (∫ x in a..(a + h), chordI g a h x) = h * ((g a + g (a + h)) / 2) :=
    integral_chordI g hh.ne'
  have hsubInt : (∫ x in a..(a + h), chordI g a h x - g x)
      = (∫ x in a..(a + h), chordI g a h x) - ∫ x in a..(a + h), g x :=
    intervalIntegral.integral_sub hIntChord hIntG
  have herr_eq : ((g a + g (a + h)) / 2) - (1 / h) * ∫ x in a..(a + h), g x
      = (1 / h) * ∫ x in a..(a + h), chordI g a h x - g x := by
    rw [hsubInt, hChordInt]; field_simp [hh.ne']
  have hpoint : ∀ x ∈ Set.uIoc a (a + h), ‖chordI g a h x - g x‖ ≤ M * h ^ 2 := by
    intro x hx
    have hxIoc : x ∈ Set.Ioc a (a + h) := by
      simpa [Set.uIoc_of_le (by linarith : a ≤ a + h)] using hx
    have hxIcc : x ∈ Set.Icc a (a + h) := ⟨le_of_lt hxIoc.1, hxIoc.2⟩
    rw [Real.norm_eq_abs]
    exact chordI_error_bound (g := g) (gp := gp) (M := M)
      hM hh ha hb hderiv hint_gp hlip hxIcc
  have hnorm : ‖∫ x in a..(a + h), chordI g a h x - g x‖ ≤ (M * h ^ 2) * |(a + h) - a| :=
    intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  calc |((g a + g (a + h)) / 2) - (1 / h) * ∫ x in a..(a + h), g x|
        = |(1 / h) * ∫ x in a..(a + h), chordI g a h x - g x| := by rw [herr_eq]
    _ = (1 / h) * ‖∫ x in a..(a + h), chordI g a h x - g x‖ := by
        rw [abs_mul, abs_of_pos (one_div_pos.mpr hh), ← Real.norm_eq_abs]
    _ ≤ (1 / h) * ((M * h ^ 2) * |(a + h) - a|) := mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = M * h ^ 2 := by rw [show (a + h) - a = h by ring, abs_of_pos hh]; field_simp [hh.ne']

end

end AnalyticCombinatorics.Ch8.Partitions
