I would not try to prove this tail theorem directly from `log1mexp_tail_bound` alone. You need the trapezoid **cell error** decay; the value bound gives integrability and summability, but not the `+ ½ f(R)` cancellation. The right proof is:

\[
E_j(a,h)=\frac{f(a+jh)+f(a+(j+1)h)}2-\frac1h\int_{a+jh}^{a+(j+1)h}f(x)\,dx,
\]
then
\[
\sum_{j\ge0} f(a+(j+1)h)-\frac1h\int_a^\infty f+\frac12f(a)
=\sum_{j\ge0}E_j(a,h),
\]
and for \(f=\log1mexp\),
\[
|E_j(a,h)|\le C e^{-(a+jh)}h^2.
\]
Since
\[
h^2\sum_{j\ge0}e^{-(a+jh)}
=h^2 e^{-a}\frac1{1-e^{-h}}
=O(h),
\]
the tail goes to zero.

The repo already uses the exact infinite-cell infrastructure needed here in `MassRateRiemannGeneral.lean`: pairwise disjoint `Ioc` cells, an `iUnion` of cells giving `Ioi 0`, and `hasSum_integral_iUnion` to decompose the set integral. fileciteturn141file0L15-L39 fileciteturn141file0L101-L124 It also uses `intervalIntegral.integral_eq_sub_of_hasDerivAt`, `intervalIntegral.abs_integral_le_integral_abs`, and `intervalIntegral.norm_integral_le_of_norm_le_const` in the same style. fileciteturn141file0L164-L170 fileciteturn142file0L29-L38

Below is the clean implementation I would add. I am flagging one thing up front: the long theorem `tail_trapezoid_identity_of_summable` is the place most likely to need minor Lean-iteration, because it combines `HasSum` algebra for three infinite objects. The lemma names used there are standard and already used in the repo (`hasSum_integral_iUnion`, `Summable.hasSum.tendsto_sum_nat`, `HasSum.tsum_eq`, `hasSum_le`, `Summable.of_nonneg_of_le`). The derivative and geometric-bound parts are straightforward.

## File: `LogOneMinusExpTail.lean`

```lean
import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.LogHeadAssembly

namespace AnalyticCombinatorics.Ch8.Partitions

open Filter Topology BigOperators MeasureTheory
open scoped Topology BigOperators Interval

noncomputable section

/-- Tail sample starting just after the head cutoff:
`∑_{j≥0} f((N+1+j)t)`. -/
noncomputable def tailLog1mexp (t : ℝ) : ℝ :=
  ∑' j : ℕ, log1mexp (((trapN t + 1 + j : ℕ) : ℝ) * t)

/-- One tail trapezoid cell error on `[a+jh, a+(j+1)h]`. -/
noncomputable def tailTrapErr (f : ℝ → ℝ) (a h : ℝ) (j : ℕ) : ℝ :=
  ((f (a + h * (j : ℝ)) + f (a + h * ((j + 1 : ℕ) : ℝ))) / 2)
    - (1 / h) * ∫ x in (a + h * (j : ℝ))..(a + h * ((j + 1 : ℕ) : ℝ)), f x

/-- Shifted tail cells. -/
def tailCell (a h : ℝ) (j : ℕ) : Set ℝ :=
  Set.Ioc (a + h * (j : ℝ)) (a + h * ((j + 1 : ℕ) : ℝ))

/-- Pairwise disjoint shifted tail cells. -/
private lemma pairwise_disjoint_tailCell {a h : ℝ} (hh : 0 ≤ h) :
    Pairwise (Disjoint on tailCell a h) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · refine Set.disjoint_left.mpr ?_
    intro x hxi hxj
    have hnat : i + 1 ≤ j := by omega
    have hreal : (((i + 1 : ℕ) : ℝ) ≤ (j : ℝ)) := by exact_mod_cast hnat
    have hle : a + h * ((i + 1 : ℕ) : ℝ) ≤ a + h * (j : ℝ) := by
      exact add_le_add_left (mul_le_mul_of_nonneg_left hreal hh) a
    exact not_lt_of_ge (hxi.2.trans hle) hxj.1
  · refine Set.disjoint_left.mpr ?_
    intro x hxi hxj
    have hnat : j + 1 ≤ i := by omega
    have hreal : (((j + 1 : ℕ) : ℝ) ≤ (i : ℝ)) := by exact_mod_cast hnat
    have hle : a + h * ((j + 1 : ℕ) : ℝ) ≤ a + h * (i : ℝ) := by
      exact add_le_add_left (mul_le_mul_of_nonneg_left hreal hh) a
    exact not_lt_of_ge (hxj.2.trans hle) hxi.1

/-- The shifted tail cells cover `Ioi a`. -/
private lemma iUnion_tailCell_eq_Ioi {a h : ℝ} (hh : 0 < h) :
    (⋃ j : ℕ, tailCell a h j) = Set.Ioi a := by
  ext x
  constructor
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨j, hj⟩
    exact lt_of_lt_of_le hj.1 (by
      have hnon : 0 ≤ h * (j : ℝ) := by positivity
      linarith)
  · intro hx
    let y : ℝ := (x - a) / h
    have hy_pos : 0 < y := by
      dsimp [y]
      exact div_pos (sub_pos.mpr hx) hh
    let n : ℕ := Nat.ceil y
    have hn_pos : 0 < n := by
      exact (Nat.ceil_pos (a := y)).mpr hy_pos
    let j : ℕ := n - 1
    have hj_succ : j + 1 = n := by dsimp [j]; omega
    have hj_lt_y : (j : ℝ) < y := by
      have hlt_nat : j < Nat.ceil y := by dsimp [j, n]; omega
      exact (Nat.lt_ceil (a := y) (n := j)).mp hlt_nat
    have hy_le_succ : y ≤ (((j + 1 : ℕ) : ℝ)) := by
      have hy_le_n : y ≤ (n : ℝ) := by
        have hnn : Nat.ceil y ≤ n := by simp [n]
        exact (Nat.ceil_le (a := y) (n := n)).mp hnn
      simpa [hj_succ] using hy_le_n
    have hmul : a + h * y = x := by
      dsimp [y]
      field_simp [hh.ne']
      ring
    refine Set.mem_iUnion.mpr ⟨j, ?_⟩
    rw [tailCell]
    constructor
    · calc
        a + h * (j : ℝ) < a + h * y := by
          exact add_lt_add_left (mul_lt_mul_of_pos_left hj_lt_y hh) a
        _ = x := hmul
    · calc
        x = a + h * y := hmul.symm
        _ ≤ a + h * ((j + 1 : ℕ) : ℝ) := by
          exact add_le_add_left (mul_le_mul_of_nonneg_left hy_le_succ hh.le) a

/-- Derivative of `log1mexp` in the convenient tail form. -/
lemma log1mexp_hasDerivAt_tail {x : ℝ} (hx : 0 < x) :
    HasDerivAt log1mexp (-(1 / (Real.exp x - 1))) x := by
  have h := log1mexp_hasDerivAt hx
  convert h using 1
  rw [Real.exp_neg]
  have hexp : Real.exp x ≠ 0 := Real.exp_ne_zero x
  have hden : Real.exp x - 1 ≠ 0 :=
    sub_ne_zero.mpr (Real.one_lt_exp_iff.mpr hx).ne'
  field_simp [hexp, hden]
  ring

/-- The tail derivative `-1/(e^x-1)` has derivative `e^x/(e^x-1)^2`. -/
lemma log1mexpDeriv_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => -(1 / (Real.exp y - 1)))
      (Real.exp x / (Real.exp x - 1) ^ 2) x := by
  have hden_deriv : HasDerivAt (fun y : ℝ => Real.exp y - 1) (Real.exp x) x := by
    simpa using (Real.hasDerivAt_exp x).sub_const 1
  have hden_ne : Real.exp x - 1 ≠ 0 :=
    sub_ne_zero.mpr (Real.one_lt_exp_iff.mpr hx).ne'
  have hinv := hden_deriv.inv hden_ne
  have hneg := hinv.neg
  convert hneg using 1
  field_simp [hden_ne]
  ring

/-- Second derivative bound: for `x ≥ log 2`,
`|log1mexp'' x| ≤ 4 e^{-x}`. -/
lemma log1mexp_second_deriv_tail_bound {x : ℝ} (hx : Real.log 2 ≤ x) :
    |Real.exp x / (Real.exp x - 1) ^ 2| ≤ 4 * Real.exp (-x) := by
  have hxpos : 0 < x := lt_of_lt_of_le (Real.log_pos (by norm_num : (1:ℝ) < 2)) hx
  have he2 : 2 ≤ Real.exp x := by
    calc
      (2 : ℝ) = Real.exp (Real.log 2) := by
        rw [Real.exp_log (by norm_num : (0:ℝ) < 2)]
      _ ≤ Real.exp x := Real.exp_le_exp.mpr hx
  have hden_half : Real.exp x / 2 ≤ Real.exp x - 1 := by linarith
  have hden_pos : 0 < Real.exp x - 1 := by
    exact sub_pos.mpr (Real.one_lt_exp_iff.mpr hxpos)
  have hden_sq : (Real.exp x / 2) ^ 2 ≤ (Real.exp x - 1) ^ 2 := by
    exact pow_le_pow_left₀ (by positivity) hden_half 2
  have hmain :
      Real.exp x / (Real.exp x - 1) ^ 2 ≤
        Real.exp x / ((Real.exp x / 2) ^ 2) := by
    exact div_le_div₀ (by positivity) le_rfl (by positivity) hden_sq
  have hsimp :
      Real.exp x / ((Real.exp x / 2) ^ 2) = 4 * Real.exp (-x) := by
    rw [Real.exp_neg]
    field_simp [Real.exp_ne_zero x]
    ring
  rw [abs_of_pos (by positivity : 0 < Real.exp x / (Real.exp x - 1) ^ 2)]
  exact hmain.trans_eq hsimp

/-- Local tail Lipschitz bound for `log1mexp'` on `[a,a+h]`. -/
lemma log1mexp_deriv_lipschitz_tail_cell
    {a h : ℝ} (hh : 0 < h) (ha : Real.log 2 ≤ a) :
    ∀ z ∈ Set.Icc a (a + h), ∀ w ∈ Set.Icc a (a + h),
      |-(1 / (Real.exp z - 1)) - -(1 / (Real.exp w - 1))|
        ≤ (4 * Real.exp (-a)) * |z - w| := by
  intro z hz w hw
  have hderiv :
      ∀ x ∈ Set.uIcc z w,
        HasDerivAt (fun y : ℝ => -(1 / (Real.exp y - 1)))
          (Real.exp x / (Real.exp x - 1) ^ 2) x := by
    intro x hx
    have hx' := Set.mem_uIcc.mp hx
    have hxge : a ≤ x := by
      rcases hx' with h | h
      · exact le_trans hz.1 h.1
      · exact le_trans hw.1 h.1
    have hxpos : 0 < x := lt_of_lt_of_le
      (Real.log_pos (by norm_num : (1:ℝ) < 2)) (le_trans ha hxge)
    exact log1mexpDeriv_hasDerivAt hxpos
  have hcont :
      ContinuousOn (fun x : ℝ => Real.exp x / (Real.exp x - 1) ^ 2) (Set.uIcc z w) := by
    intro x hx
    have hx' := Set.mem_uIcc.mp hx
    have hxge : a ≤ x := by
      rcases hx' with h | h
      · exact le_trans hz.1 h.1
      · exact le_trans hw.1 h.1
    have hxpos : 0 < x := lt_of_lt_of_le
      (Real.log_pos (by norm_num : (1:ℝ) < 2)) (le_trans ha hxge)
    have hden : (Real.exp x - 1) ^ 2 ≠ 0 := by
      have : 0 < Real.exp x - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hxpos)
      positivity
    exact ((Real.continuous_exp.continuousAt).div
      (((Real.continuous_exp.sub continuous_const).pow 2).continuousAt) hden).continuousWithinAt
  have hint :
      IntervalIntegrable (fun x : ℝ => Real.exp x / (Real.exp x - 1) ^ 2)
        MeasureTheory.volume z w :=
    hcont.intervalIntegrable
  have hFTC :
      (∫ x in z..w, Real.exp x / (Real.exp x - 1) ^ 2)
        = (-(1 / (Real.exp w - 1))) - (-(1 / (Real.exp z - 1))) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hpoint :
      ∀ x ∈ Set.uIoc z w,
        ‖Real.exp x / (Real.exp x - 1) ^ 2‖ ≤ 4 * Real.exp (-a) := by
    intro x hx
    have hx' := Set.mem_uIoc.mp hx
    have hxge : a ≤ x := by
      rcases hx' with h | h
      · exact le_trans hz.1 (le_of_lt h.1)
      · exact le_trans hw.1 (le_of_lt h.1)
    rw [Real.norm_eq_abs]
    calc
      |Real.exp x / (Real.exp x - 1) ^ 2| ≤ 4 * Real.exp (-x) :=
        log1mexp_second_deriv_tail_bound (le_trans ha hxge)
      _ ≤ 4 * Real.exp (-a) := by
        gcongr
        exact Real.exp_le_exp.mpr (by linarith)
  have hnorm :
      ‖∫ x in z..w, Real.exp x / (Real.exp x - 1) ^ 2‖
        ≤ (4 * Real.exp (-a)) * |w - z| :=
    intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  calc
    |-(1 / (Real.exp z - 1)) - -(1 / (Real.exp w - 1))|
        = ‖∫ x in z..w, Real.exp x / (Real.exp x - 1) ^ 2‖ := by
          rw [hFTC, Real.norm_eq_abs, abs_sub_comm]
    _ ≤ (4 * Real.exp (-a)) * |w - z| := hnorm
    _ = (4 * Real.exp (-a)) * |z - w| := by rw [abs_sub_comm]

```

Now the cell trapezoid bound. This deliberately mirrors your existing `TrapezoidCell` chord proof, but with a local Lipschitz constant. It is better to put it in `TrapezoidTail.lean` and reuse it for other tails.

```lean
/-- Local per-cell trapezoid bound from a local Lipschitz derivative. -/
theorem cell_trapezoid_bound_of_local_lipschitz_deriv
    {g gp : ℝ → ℝ} {L a h : ℝ}
    (hL : 0 ≤ L) (hh : 0 < h)
    (hderiv : ∀ x ∈ Set.Icc a (a + h), HasDerivAt g (gp x) x)
    (hint_g : IntervalIntegrable g MeasureTheory.volume a (a + h))
    (hint_gp : IntervalIntegrable gp MeasureTheory.volume a (a + h))
    (hlip : ∀ z ∈ Set.Icc a (a + h), ∀ w ∈ Set.Icc a (a + h),
      |gp z - gp w| ≤ L * |z - w|) :
    |((g a + g (a + h)) / 2) - (1 / h) * ∫ x in a..(a + h), g x|
      ≤ L * h ^ 2 := by
  -- This is exactly the proof of `cell_trapezoid_bound_of_lipschitz_deriv_Ioc`
  -- with `Set.Icc a (a+h)` replacing the fixed domain.
  -- The shortest stable implementation is to copy `TrapezoidCellIoc.lean`'s
  -- `chordI`, `first_order_error_Ioc`, `chordI_error_bound`, and final theorem,
  -- replacing membership in `Set.Ioc 0 2` by membership in `Set.Icc a (a+h)`.
  -- All algebraic lines are unchanged.
  --
  -- If you do not want duplicated code, refactor `TrapezoidCellIoc.lean` to expose
  -- this local theorem and then derive the Ioc version from it.
  exact by
    -- Keep this theorem as a refactor target; the proof is a syntactic specialization
    -- of your already-green `TrapezoidCellIoc`.
    sorry
```

I am not going to pretend the last proof can be made “complete” in a few lines: it is a refactor of your already-green chord proof, not a new mathematical idea. The honest shortest path is to move the private local proof out of `TrapezoidCellIoc.lean` into this local-domain theorem; then the Ioc theorem and the tail theorem both call it. This avoids duplicating 120 lines of chord algebra.

Once that local theorem exists, the concrete tail cell bound is short:

```lean
/-- Tail cell trapezoid bound for `log1mexp`: `≤ 4 e^{-a} h²`. -/
lemma log1mexp_tail_cell_bound
    {a h : ℝ} (hh : 0 < h) (ha : Real.log 2 ≤ a) :
    |((log1mexp a + log1mexp (a + h)) / 2)
        - (1 / h) * ∫ x in a..(a + h), log1mexp x|
      ≤ (4 * Real.exp (-a)) * h ^ 2 := by
  have hL : 0 ≤ 4 * Real.exp (-a) := by positivity
  have hderiv :
      ∀ x ∈ Set.Icc a (a + h),
        HasDerivAt log1mexp (-(1 / (Real.exp x - 1))) x := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le
      (Real.log_pos (by norm_num : (1:ℝ) < 2)) (le_trans ha hx.1)
    exact log1mexp_hasDerivAt_tail hxpos
  have hint_g : IntervalIntegrable log1mexp MeasureTheory.volume a (a + h) := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le (by linarith : a ≤ a + h)] at hx
    exact (log1mexp_hasDerivAt_tail
      (lt_of_lt_of_le (Real.log_pos (by norm_num : (1:ℝ) < 2)) (le_trans ha hx.1))).continuousAt.continuousWithinAt
  have hint_gp :
      IntervalIntegrable (fun x : ℝ => -(1 / (Real.exp x - 1)))
        MeasureTheory.volume a (a + h) := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le (by linarith : a ≤ a + h)] at hx
    have hxpos : 0 < x := lt_of_lt_of_le
      (Real.log_pos (by norm_num : (1:ℝ) < 2)) (le_trans ha hx.1)
    have hden : Real.exp x - 1 ≠ 0 :=
      sub_ne_zero.mpr (Real.one_lt_exp_iff.mpr hxpos).ne'
    exact ((continuous_const.div ((Real.continuous_exp.sub continuous_const)) hden).neg
      ).continuousAt.continuousWithinAt
  have hlip :=
    log1mexp_deriv_lipschitz_tail_cell (a := a) (h := h) hh ha
  exact cell_trapezoid_bound_of_local_lipschitz_deriv
    (g := log1mexp) (gp := fun x => -(1 / (Real.exp x - 1)))
    (L := 4 * Real.exp (-a)) (a := a) (h := h)
    hL hh hderiv hint_g hint_gp hlip
```

## Infinite-cell tail theorem

The next theorem is the infinite-cell summation. This is the part modeled on `MassRateRiemannGeneral.lean`.

```lean
/-- Geometric error sum bound used in the tail. -/
lemma exp_tail_geometric_bound {a h : ℝ} (hh : 0 < h) :
    (∑' j : ℕ, Real.exp (-(a + h * (j : ℝ))))
      = Real.exp (-a) / (1 - Real.exp (-h)) := by
  have hr0 : 0 ≤ Real.exp (-h) := (Real.exp_pos _).le
  have hr1 : Real.exp (-h) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hs :
      (∑' j : ℕ, Real.exp (-a) * (Real.exp (-h)) ^ j)
        = Real.exp (-a) * (1 / (1 - Real.exp (-h))) := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  convert hs using 1
  · ext j
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    ring
  · field_simp

/-- For `0 < h ≤ 1`, `1 - e^{-h} ≥ h / 2`. -/
lemma one_sub_exp_neg_ge_half {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) :
    h / 2 ≤ 1 - Real.exp (-h) := by
  have hexp_le : Real.exp (-h) ≤ 1 / (1 + h) := by
    rw [Real.exp_neg]
    exact one_div_le_one_div_of_le (by positivity) (Real.add_one_le_exp h)
  have hbase : 1 - 1 / (1 + h) = h / (1 + h) := by
    field_simp
    ring
  have hhalf : h / 2 ≤ h / (1 + h) := by
    rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 2) (by positivity : 0 < 1 + h)]
    nlinarith
  linarith

/--
Generic tail trapezoid theorem from exponentially decaying cell errors.

This theorem assumes:
* `f` is integrable on `Ioi a`;
* the samples are summable;
* `f(a+n h) → 0`;
* each trapezoid cell error is bounded by `C e^{-(a+jh)} h²`.

The conclusion is the exact right-endpoint tail expression.
-/
theorem tail_trapezoid_bound_of_exp_cell_errors
    {f : ℝ → ℝ} {a h C : ℝ}
    (hh : 0 < h) (hC : 0 ≤ C)
    (hfint : IntegrableOn f (Set.Ioi a))
    (hsamp : Summable (fun j : ℕ => f (a + h * ((j + 1 : ℕ) : ℝ))))
    (hzero : Tendsto (fun n : ℕ => f (a + h * (n : ℝ))) atTop (𝓝 0))
    (hcell :
      ∀ j : ℕ,
        |tailTrapErr f a h j| ≤ C * Real.exp (-(a + h * (j : ℝ))) * h ^ 2) :
    |(∑' j : ℕ, f (a + h * ((j + 1 : ℕ) : ℝ)))
        - (1 / h) * ∫ x in Set.Ioi a, f x
        + (1 / 2) * f a|
      ≤ C * h ^ 2 * (Real.exp (-a) / (1 - Real.exp (-h))) := by
  classical

  -- Cell integral decomposition of `∫_{a}^{∞}`.
  let B : ℕ → ℝ := fun j =>
    ∫ x in tailCell a h j, f x
  have hUnion : (⋃ j : ℕ, tailCell a h j) = Set.Ioi a :=
    iUnion_tailCell_eq_Ioi (a := a) (h := h) hh
  have hpair : Pairwise (Disjoint on tailCell a h) :=
    pairwise_disjoint_tailCell (a := a) (h := h) hh.le
  have hmeas : ∀ j : ℕ, MeasurableSet (tailCell a h j) := by
    intro j
    simp [tailCell]
  have hB_has :
      HasSum B (∫ x in Set.Ioi a, f x) := by
    have h_int_union : IntegrableOn f (⋃ j : ℕ, tailCell a h j) := by
      simpa [hUnion] using hfint
    simpa [B, hUnion] using
      (hasSum_integral_iUnion (μ := volume) (f := f) hmeas hpair h_int_union)

  -- Absolute summability of cell errors from the exponential majorant.
  have hgeom_summ :
      Summable (fun j : ℕ => C * Real.exp (-(a + h * (j : ℝ))) * h ^ 2) := by
    have hr0 : 0 ≤ Real.exp (-h) := (Real.exp_pos _).le
    have hr1 : Real.exp (-h) < 1 := by
      rw [Real.exp_lt_one_iff]
      linarith
    have hgeo : Summable (fun j : ℕ => (Real.exp (-h)) ^ j) :=
      summable_geometric_of_lt_one hr0 hr1
    refine hgeo.mul_left (C * Real.exp (-a) * h ^ 2) |>.congr ?_
    intro j
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    push_cast
    ring

  have herr_abs_summ :
      Summable (fun j : ℕ => |tailTrapErr f a h j|) :=
    Summable.of_nonneg_of_le
      (fun j => abs_nonneg _)
      hcell
      hgeom_summ
  have herr_summ : Summable (tailTrapErr f a h) :=
    Summable.of_abs herr_abs_summ

  -- The finite partial identity:
  -- `∑_{j<N} err_j = ∑_{j<N} f(a+(j+1)h) - (1/h)∑_{j<N}B_j
  --                  + 1/2 f(a) - 1/2 f(a+Nh)`.
  have hpartial :
      ∀ N : ℕ,
        (∑ j ∈ Finset.range N, tailTrapErr f a h j)
          =
        (∑ j ∈ Finset.range N, f (a + h * ((j + 1 : ℕ) : ℝ)))
          - (1 / h) * (∑ j ∈ Finset.range N, B j)
          + (1 / 2) * f a
          - (1 / 2) * f (a + h * (N : ℝ)) := by
    intro N
    unfold tailTrapErr B
    rw [Finset.sum_sub_distrib]
    rw [Finset.mul_sum]
    have htrap :
        (∑ j ∈ Finset.range N,
          (f (a + h * (j : ℝ)) + f (a + h * ((j + 1 : ℕ) : ℝ))) / 2)
        =
        (∑ j ∈ Finset.range N, f (a + h * ((j + 1 : ℕ) : ℝ)))
          + (1 / 2) * f a
          - (1 / 2) * f (a + h * (N : ℝ)) := by
      -- telescoping endpoint identity
      have hshift :=
        sum_range_succ_sub_sum_range
          (fun n : ℕ => f (a + h * (n : ℝ))) N
      have hsplit :
          (∑ j ∈ Finset.range N,
            (f (a + h * (j : ℝ)) + f (a + h * ((j + 1 : ℕ) : ℝ))) / 2)
          =
          ((∑ j ∈ Finset.range N, f (a + h * (j : ℝ)))
            + (∑ j ∈ Finset.range N, f (a + h * ((j + 1 : ℕ) : ℝ)))) / 2 := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_div]
      rw [hsplit]
      simp only [Nat.cast_zero, mul_zero, add_zero] at hshift
      linarith
    rw [htrap]
    ring

  -- Pass finite partial identity to the limit.
  have hleft_lim :
      Tendsto
        (fun N : ℕ => ∑ j ∈ Finset.range N, tailTrapErr f a h j)
        atTop (𝓝 (∑' j : ℕ, tailTrapErr f a h j)) :=
    herr_summ.hasSum.tendsto_sum_nat

  have hsamp_lim :
      Tendsto
        (fun N : ℕ => ∑ j ∈ Finset.range N, f (a + h * ((j + 1 : ℕ) : ℝ)))
        atTop (𝓝 (∑' j : ℕ, f (a + h * ((j + 1 : ℕ) : ℝ)))) :=
    hsamp.hasSum.tendsto_sum_nat

  have hB_lim :
      Tendsto (fun N : ℕ => ∑ j ∈ Finset.range N, B j)
        atTop (𝓝 (∫ x in Set.Ioi a, f x)) :=
    hB_has.tendsto_sum_nat

  have hend_lim :
      Tendsto (fun N : ℕ => f (a + h * (N : ℝ))) atTop (𝓝 0) :=
    hzero

  have hright_lim :
      Tendsto
        (fun N : ℕ =>
          (∑ j ∈ Finset.range N, f (a + h * ((j + 1 : ℕ) : ℝ)))
            - (1 / h) * (∑ j ∈ Finset.range N, B j)
            + (1 / 2) * f a
            - (1 / 2) * f (a + h * (N : ℝ)))
        atTop
        (𝓝 ((∑' j : ℕ, f (a + h * ((j + 1 : ℕ) : ℝ)))
          - (1 / h) * ∫ x in Set.Ioi a, f x
          + (1 / 2) * f a
          - (1 / 2) * 0)) := by
    exact (((hsamp_lim.sub (hB_lim.const_mul (1 / h))).add_const ((1 / 2) * f a))
      .sub (hend_lim.const_mul (1 / 2)))

  have htsum_eq :
      (∑' j : ℕ, tailTrapErr f a h j)
        =
      (∑' j : ℕ, f (a + h * ((j + 1 : ℕ) : ℝ)))
          - (1 / h) * ∫ x in Set.Ioi a, f x
          + (1 / 2) * f a := by
    have heq_lim := tendsto_nhds_unique hleft_lim
      (hright_lim.congr' (Eventually.of_forall hpartial))
    simpa using heq_lim

  -- Bound the tsum of errors by the geometric majorant.
  have hsum_abs :
      |∑' j : ℕ, tailTrapErr f a h j|
        ≤ ∑' j : ℕ, |tailTrapErr f a h j| := by
    exact abs_tsum_le_tsum_abs herr_abs_summ

  have hgeom_bound :
      (∑' j : ℕ, |tailTrapErr f a h j|)
        ≤ ∑' j : ℕ, C * Real.exp (-(a + h * (j : ℝ))) * h ^ 2 := by
    exact Summable.tsum_le_tsum hcell herr_abs_summ hgeom_summ

  have hgeom_eval :
      (∑' j : ℕ, C * Real.exp (-(a + h * (j : ℝ))) * h ^ 2)
        =
      C * h ^ 2 * (Real.exp (-a) / (1 - Real.exp (-h))) := by
    rw [show (fun j : ℕ => C * Real.exp (-(a + h * (j : ℝ))) * h ^ 2)
        = fun j : ℕ => (C * h ^ 2) * Real.exp (-(a + h * (j : ℝ))) by
      funext j; ring]
    rw [tsum_mul_left, exp_tail_geometric_bound (a := a) (h := h) hh]
    ring

  rw [← htsum_eq]
  exact hsum_abs.trans (hgeom_bound.trans_eq hgeom_eval)
```

`abs_tsum_le_tsum_abs` may be named slightly differently in your Mathlib. If it is unavailable, use the same two-sided `hasSum_le` argument from `MassRateRiemannGeneral.lean`, lines 116–135. fileciteturn142file0L116-L135

## Concrete `log1mexp` tail theorem

Now instantiate with `a = trapR t`, `h = t`, `C = 4`.

```lean
/-- Integrability of `log1mexp` on an exponential tail. -/
lemma log1mexp_integrableOn_Ioi_tail {a : ℝ} (ha : Real.log 2 ≤ a) :
    IntegrableOn log1mexp (Set.Ioi a) := by
  have hmeas : AEStronglyMeasurable log1mexp (volume.restrict (Set.Ioi a)) := by
    unfold log1mexp
    measurability
  have hdom : IntegrableOn (fun x : ℝ => 2 * Real.exp (-x)) (Set.Ioi a) := by
    have hbase : IntegrableOn (fun x : ℝ => Real.exp (-x)) (Set.Ioi a) := by
      have h := exp_neg_integrableOn_Ioi a one_pos
      simpa [one_mul] using h
    exact hbase.const_mul 2
  apply Integrable.mono' hdom hmeas
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards with x hx
  rw [Real.norm_eq_abs]
  exact log1mexp_tail_bound (le_trans ha hx.le)

/-- Tail samples are summable once the tail starts at `a ≥ log 2`. -/
lemma summable_log1mexp_tail_samples {a h : ℝ} (ha : Real.log 2 ≤ a) (hh : 0 < h) :
    Summable (fun j : ℕ => log1mexp (a + h * ((j + 1 : ℕ) : ℝ))) := by
  have hr0 : 0 ≤ Real.exp (-h) := (Real.exp_pos _).le
  have hr1 : Real.exp (-h) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hgeo : Summable (fun j : ℕ => 2 * Real.exp (-(a + h)) * (Real.exp (-h)) ^ j) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  refine Summable.of_norm_bounded hgeo ?_
  intro j
  have hx : Real.log 2 ≤ a + h * ((j + 1 : ℕ) : ℝ) := by
    have hnon : 0 ≤ h * ((j + 1 : ℕ) : ℝ) := by positivity
    linarith
  rw [Real.norm_eq_abs]
  calc
    |log1mexp (a + h * ((j + 1 : ℕ) : ℝ))|
        ≤ 2 * Real.exp (-(a + h * ((j + 1 : ℕ) : ℝ))) :=
          log1mexp_tail_bound hx
    _ = 2 * Real.exp (-(a + h)) * (Real.exp (-h)) ^ j := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      push_cast
      ring

/-- Tail samples tend to zero. -/
lemma log1mexp_tail_samples_tendsto_zero {a h : ℝ} (ha : Real.log 2 ≤ a) (hh : 0 < h) :
    Tendsto (fun n : ℕ => log1mexp (a + h * (n : ℝ))) atTop (𝓝 0) := by
  have hx : Tendsto (fun n : ℕ => a + h * (n : ℝ)) atTop atTop := by
    exact tendsto_const_nhds.atTop_add (tendsto_natCast_atTop_atTop.const_mul_atTop hh)
  have hbound :
      ∀ᶠ n : ℕ in atTop,
        ‖log1mexp (a + h * (n : ℝ))‖ ≤ 2 * Real.exp (-(a + h * (n : ℝ))) := by
    filter_upwards [eventually_ge_atTop 0] with n _hn
    have hxge : Real.log 2 ≤ a + h * (n : ℝ) := by
      have hnon : 0 ≤ h * (n : ℝ) := by positivity
      linarith
    rw [Real.norm_eq_abs]
    exact log1mexp_tail_bound hxge
  have hzero :
      Tendsto (fun n : ℕ => 2 * Real.exp (-(a + h * (n : ℝ)))) atTop (𝓝 0) := by
    have hreal : Tendsto (fun x : ℝ => 2 * Real.exp (-x)) atTop (𝓝 0) := by
      simpa using (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot)).const_mul 2
    exact hreal.comp hx
  exact squeeze_zero_norm' hbound hzero

/-- The geometric tail error bound is `O(t)` near zero. -/
lemma tail_geometric_error_tendsto_zero :
    Tendsto
      (fun t : ℝ =>
        (4 : ℝ) * t ^ 2 * (Real.exp (-(trapR t)) / (1 - Real.exp (-t))))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hbound :
      ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
        ‖(4 : ℝ) * t ^ 2 * (Real.exp (-(trapR t)) / (1 - Real.exp (-t)))‖ ≤ 8 * t := by
    filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))]
      with t ht ht1
    have htpos : 0 < t := ht
    have htle : t ≤ 1 := le_of_lt ht1
    have hden : t / 2 ≤ 1 - Real.exp (-t) := one_sub_exp_neg_ge_half htpos htle
    have hdenpos : 0 < 1 - Real.exp (-t) := by linarith
    have hexp_le_one : Real.exp (-(trapR t)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have hRnn : 0 ≤ trapR t := by rw [trapR]; positivity
      linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc
      (4 : ℝ) * t ^ 2 * (Real.exp (-(trapR t)) / (1 - Real.exp (-t)))
          ≤ 4 * t ^ 2 * (1 / (t / 2)) := by
            gcongr
            · exact hexp_le_one
            · exact hden
      _ = 8 * t := by
            field_simp [htpos.ne']
            ring
  have ht : Tendsto (fun t : ℝ => 8 * t) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    simpa using h.const_mul (8 : ℝ)
  exact squeeze_zero_norm' hbound ht

/--
**Tail trapezoid theorem for `log1mexp`.**

Right-endpoint infinite tail after the head cutoff:
`∑_{j≥0} f((N+1+j)t) − (1/t)∫_{R}^{∞}f + ½f(R) → 0`.
-/
theorem log1mexp_tail_trapezoid :
    Tendsto
      (fun t : ℝ =>
        (∑' j : ℕ, log1mexp (((trapN t + 1 + j : ℕ) : ℝ) * t))
          - (1 / t) * ∫ x in Set.Ioi (trapR t), log1mexp x
          + (1 / 2 : ℝ) * log1mexp (trapR t))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hbound :
      ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
        ‖(∑' j : ℕ, log1mexp (((trapN t + 1 + j : ℕ) : ℝ) * t))
          - (1 / t) * ∫ x in Set.Ioi (trapR t), log1mexp x
          + (1 / 2 : ℝ) * log1mexp (trapR t)‖
        ≤ (4 : ℝ) * t ^ 2 * (Real.exp (-(trapR t)) / (1 - Real.exp (-t))) := by
    filter_upwards [self_mem_nhdsWithin,
        trapR_tendsto_one.eventually_ge_atTop (Real.log 2)]
      with t ht hRlog2
    have htpos : 0 < t := ht
    have hcell : ∀ j : ℕ,
        |tailTrapErr log1mexp (trapR t) t j|
          ≤ 4 * Real.exp (-(trapR t + t * (j : ℝ))) * t ^ 2 := by
      intro j
      exact log1mexp_tail_cell_bound
        (hh := htpos)
        (ha := by
          have hnon : 0 ≤ t * (j : ℝ) := by positivity
          linarith [hRlog2])
    have htail :=
      tail_trapezoid_bound_of_exp_cell_errors
        (f := log1mexp) (a := trapR t) (h := t) (C := (4 : ℝ))
        htpos (by norm_num)
        (log1mexp_integrableOn_Ioi_tail hRlog2)
        (summable_log1mexp_tail_samples hRlog2 htpos)
        (log1mexp_tail_samples_tendsto_zero hRlog2 htpos)
        hcell
    -- Rewrite the theorem's samples as `R + t*(j+1)`.
    have hsamp :
        (fun j : ℕ => log1mexp (((trapN t + 1 + j : ℕ) : ℝ) * t))
          =
        (fun j : ℕ => log1mexp (trapR t + t * ((j + 1 : ℕ) : ℝ))) := by
      funext j
      rw [trapR]
      congr 1
      push_cast
      ring
    simpa [hsamp, Real.norm_eq_abs, one_div] using htail

  exact squeeze_zero_norm' hbound tail_geometric_error_tendsto_zero
```

## What is confirmed versus likely-to-iterate

Confirmed from repo/current files:

* `log1mexp_tail_bound` is available with the stated exponential value bound. fileciteturn118file0L55-L58
* `log1mexp_hasDerivAt` is available, and converts to the tail derivative form. fileciteturn118file0L78-L92
* `trapR_tendsto_one` is available in `StirlingHead.lean`. fileciteturn140file0L24-L46
* The infinite-cell proof pattern and lemmas are already used in `MassRateRiemannGeneral.lean`: `hasSum_integral_iUnion`, `Summable.of_nonneg_of_le`, `HasSum.tsum_eq`, and `norm_integral_le_of_norm_le_const`. fileciteturn141file0L101-L124 fileciteturn142file0L75-L109
* `summable_geometric_of_lt_one` is used in the repo. fileciteturn124file0L49-L51

Likely iteration points:

* `abs_tsum_le_tsum_abs`: if unavailable under that exact name, replace it with the two-sided `hasSum_le` proof in `MassRateRiemannGeneral.lean`, lines 116–135. fileciteturn142file0L116-L135
* `cell_trapezoid_bound_of_local_lipschitz_deriv`: implement by refactoring your already-green `TrapezoidCellIoc.lean` chord proof into a local-domain theorem. This is the only place I intentionally did not duplicate 100+ lines of existing algebra in the answer; mathematically it is exactly the same theorem with the fixed domain replaced by `Set.Icc a (a+h)`.

Once that local-domain cell producer is exposed, the rest of the file above is the tail theorem you need.
