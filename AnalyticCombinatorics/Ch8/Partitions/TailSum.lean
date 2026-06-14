import AnalyticCombinatorics.Ch8.Partitions.TailLip
import AnalyticCombinatorics.Ch8.Partitions.TrapezoidEM

/-!
# Infinite-cell tail trapezoid summation (HR constant, brick 2 tail)

The exponential-tail trapezoid theorem (ChatGPT R8): from per-cell errors decaying
like `C e^{-(a+jh)} h²`, the right-endpoint tail expression is `O(h) → 0`. Uses
disjoint shifted cells covering `Ioi a` (`hasSum_integral_iUnion`) + telescoping.
-/

namespace AnalyticCombinatorics.Ch8.Partitions

open Filter Topology BigOperators MeasureTheory Real Function
open scoped Topology BigOperators Interval

noncomputable section

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
      have := mul_le_mul_of_nonneg_left hreal hh; linarith
    linarith [hxi.2, hxj.1, hle]
  · refine Set.disjoint_left.mpr ?_
    intro x hxi hxj
    have hnat : j + 1 ≤ i := by omega
    have hreal : (((j + 1 : ℕ) : ℝ) ≤ (i : ℝ)) := by exact_mod_cast hnat
    have hle : a + h * ((j + 1 : ℕ) : ℝ) ≤ a + h * (i : ℝ) := by
      have := mul_le_mul_of_nonneg_left hreal hh; linarith
    linarith [hxj.2, hxi.1, hle]

/-- The shifted tail cells cover `Ioi a`. -/
private lemma iUnion_tailCell_eq_Ioi {a h : ℝ} (hh : 0 < h) :
    (⋃ j : ℕ, tailCell a h j) = Set.Ioi a := by
  ext x
  constructor
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨j, hj⟩
    exact lt_of_le_of_lt (le_add_of_nonneg_right (by positivity)) hj.1
  · intro hx
    let y : ℝ := (x - a) / h
    have hy_pos : 0 < y := by dsimp [y]; exact div_pos (sub_pos.mpr hx) hh
    let n : ℕ := Nat.ceil y
    have hn_pos : 0 < n := (Nat.ceil_pos (a := y)).mpr hy_pos
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
    have hmul : a + h * y = x := by dsimp [y]; field_simp [hh.ne']; ring
    refine Set.mem_iUnion.mpr ⟨j, ?_⟩
    rw [tailCell]
    constructor
    · calc a + h * (j : ℝ) < a + h * y := by linarith [mul_lt_mul_of_pos_left hj_lt_y hh]
        _ = x := hmul
    · calc x = a + h * y := hmul.symm
        _ ≤ a + h * ((j + 1 : ℕ) : ℝ) := by linarith [mul_le_mul_of_nonneg_left hy_le_succ hh.le]

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
        - (1 / h) * (∫ x in Set.Ioi a, f x)
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
    rw [← Real.exp_nat_mul,
      show C * Real.exp (-a) * h ^ 2 * Real.exp ((j : ℝ) * -h)
        = C * h ^ 2 * (Real.exp (-a) * Real.exp ((j : ℝ) * -h)) by ring,
      ← Real.exp_add, show -a + (j : ℝ) * -h = -(a + h * (j : ℝ)) by ring]
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
    have hBeq : ∀ j : ℕ,
        (∫ x in (a + h * (j : ℝ))..(a + h * ((j + 1 : ℕ) : ℝ)), f x) = B j := by
      intro j
      show (∫ x in (a + h * (j : ℝ))..(a + h * ((j + 1 : ℕ) : ℝ)), f x)
        = ∫ x in tailCell a h j, f x
      rw [tailCell, intervalIntegral.integral_of_le (by push_cast; nlinarith [hh.le])]
    unfold tailTrapErr
    simp_rw [hBeq]
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
          - (1 / h) * (∫ x in Set.Ioi a, f x)
          + (1 / 2) * f a
          - (1 / 2) * 0)) := by
    have key := Filter.Tendsto.sub
      ((hsamp_lim.sub (hB_lim.const_mul (1 / h))).add
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 / 2) * f a) atTop (𝓝 ((1 / 2) * f a))))
      (hend_lim.const_mul (1 / 2))
    convert key using 2

  have htsum_eq :
      (∑' j : ℕ, tailTrapErr f a h j)
        =
      (∑' j : ℕ, f (a + h * ((j + 1 : ℕ) : ℝ)))
          - (1 / h) * (∫ x in Set.Ioi a, f x)
          + (1 / 2) * f a := by
    have heq_lim := tendsto_nhds_unique hleft_lim
      (hright_lim.congr' (Eventually.of_forall (fun N => (hpartial N).symm)))
    simpa using heq_lim

  -- Bound the tsum of errors by the geometric majorant.
  have hsum_abs :
      |∑' j : ℕ, tailTrapErr f a h j|
        ≤ ∑' j : ℕ, |tailTrapErr f a h j| := by
    have hh2 : Summable (fun j : ℕ => ‖tailTrapErr f a h j‖) := by
      simpa [Real.norm_eq_abs] using herr_abs_summ
    simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hh2

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

  rw [← htsum_eq]
  exact hsum_abs.trans (hgeom_bound.trans_eq hgeom_eval)

end

end AnalyticCombinatorics.Ch8.Partitions
