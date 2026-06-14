import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.LogRegCell
import AnalyticCombinatorics.Ch8.Partitions.TrapezoidEM

/-!
# Open-left head trapezoid theorem (HR constant, brick 2)

Peels the first cell `[0,t]` (controlled by `log1mexpReg_tendsto_zero`, avoiding the
derivative at `0`) and applies the open-left per-cell bound only on cells `k ≥ 1`.
Yields the head asymptotic for `log1mexpReg` (ChatGPT R6).
-/

namespace AnalyticCombinatorics.Ch8.Partitions

open Filter Topology BigOperators
open scoped Topology BigOperators Interval

noncomputable section

/-- The first-cell trapezoid error. -/
noncomputable def firstCellTrapErr (g : ℝ → ℝ) (t : ℝ) : ℝ :=
  ((g 0 + g t) / 2) - (1 / t) * ∫ x in (0 : ℝ)..t, g x

/-- `log1mexpReg 0 = 0` (Lean's total `Real.log 0 = 0`). -/
lemma log1mexpReg_zero : log1mexpReg 0 = 0 := by
  simp [log1mexpReg, log1mexp]

/-- If `g → 0` from the right at `0` and `g 0 = 0`, the first-cell error → 0. -/
theorem firstCellTrapErr_tendsto_zero {g : ℝ → ℝ}
    (hg0 : g 0 = 0) (hg : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Tendsto (firstCellTrapErr g) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  classical
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε4 : 0 < ε / 4 := by positivity
  have hpre : {x : ℝ | ‖g x‖ < ε / 4} ∈ 𝓝[>] (0 : ℝ) := by
    have hb : Metric.ball (0 : ℝ) (ε / 4) ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds 0 hε4
    refine Filter.mem_of_superset (hg hb) (fun x hx => ?_)
    rw [Set.mem_preimage, mem_ball_zero_iff] at hx
    exact hx
  rw [Metric.mem_nhdsWithin_iff] at hpre
  rcases hpre with ⟨δ, hδ, hδsub⟩
  have htSmall : Set.Ioo (0 : ℝ) δ ∈ 𝓝[>] (0 : ℝ) := by
    have h1 : Set.Iio δ ∈ 𝓝[>] (0 : ℝ) := mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδ)
    have h2 : (Set.Iio δ ∩ Set.Ioi (0 : ℝ)) = Set.Ioo 0 δ := by
      ext y; simp [Set.mem_Ioo, and_comm]
    rw [← h2]; exact Filter.inter_mem h1 self_mem_nhdsWithin
  filter_upwards [self_mem_nhdsWithin, htSmall] with t ht htδ
  have htpos : 0 < t := ht
  have htδ' : t < δ := htδ.2
  have hsmall : ∀ x ∈ Set.Ioc (0 : ℝ) t, ‖g x‖ ≤ ε / 4 := by
    intro x hx
    have hxmem : x ∈ Metric.ball (0 : ℝ) δ ∩ Set.Ioi (0 : ℝ) := by
      refine ⟨?_, hx.1⟩
      rw [Metric.mem_ball, dist_eq_norm, sub_zero, Real.norm_eq_abs, abs_of_pos hx.1]
      exact lt_of_le_of_lt hx.2 htδ'
    exact le_of_lt (hδsub hxmem)
  have hgt : ‖g t‖ ≤ ε / 4 := hsmall t ⟨htpos, le_rfl⟩
  have hInt : ‖∫ x in (0 : ℝ)..t, g x‖ ≤ (ε / 4) * |t - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
    intro x hx
    have hxIoc : x ∈ Set.Ioc (0 : ℝ) t := by simpa [Set.uIoc_of_le htpos.le] using hx
    exact hsmall x hxIoc
  have havg : ‖(1 / t) * ∫ x in (0 : ℝ)..t, g x‖ ≤ ε / 4 := by
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr htpos)]
    calc (1 / t) * ‖∫ x in (0 : ℝ)..t, g x‖
          ≤ (1 / t) * ((ε / 4) * |t - 0|) := mul_le_mul_of_nonneg_left hInt (by positivity)
      _ = ε / 4 := by rw [sub_zero, abs_of_pos htpos]; field_simp [htpos.ne']
  have hmain : ‖firstCellTrapErr g t‖ ≤ ε / 2 := by
    unfold firstCellTrapErr
    rw [hg0]
    have hhalf : ‖(0 + g t) / 2‖ ≤ ε / 8 := by
      rw [zero_add, norm_div]
      have h2 : ‖(2 : ℝ)‖ = 2 := by norm_num
      rw [h2]; nlinarith [hgt, norm_nonneg (g t)]
    calc ‖(0 + g t) / 2 - (1 / t) * ∫ x in (0 : ℝ)..t, g x‖
          ≤ ‖(0 + g t) / 2‖ + ‖(1 / t) * ∫ x in (0 : ℝ)..t, g x‖ := by
            simpa [sub_eq_add_neg] using
              norm_add_le ((0 + g t) / 2) (-((1 / t) * ∫ x in (0 : ℝ)..t, g x))
      _ ≤ ε / 8 + ε / 4 := add_le_add hhalf havg
      _ ≤ ε / 2 := by linarith
  rw [dist_eq_norm, sub_zero]
  exact lt_of_le_of_lt hmain (by linarith)

/-- First-cell estimate for `log1mexpReg`. -/
theorem log1mexpReg_first_cell_tendsto_zero :
    Tendsto (firstCellTrapErr log1mexpReg) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  firstCellTrapErr_tendsto_zero log1mexpReg_zero log1mexpReg_tendsto_zero

/-- Open-left head theorem (range form): peel cell 0, apply `hcell_pos` on `k ≥ 1`. -/
theorem trapezoid_head_range_tendsto_of_cell_bound_pos
    {g : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hint : ∀ ⦃a b : ℝ⦄, 0 ≤ a → b ≤ 2 →
        IntervalIntegrable g MeasureTheory.volume a b)
    (hfirst : Tendsto (firstCellTrapErr g) (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hcell_pos : ∀ ⦃a h : ℝ⦄, 0 < h → 0 < a → a + h ≤ 2 →
        |((g a + g (a + h)) / 2) - (1 / h) * ∫ x in a..(a + h), g x| ≤ M * h ^ 2) :
    Tendsto
      (fun t : ℝ =>
        (∑ k ∈ Finset.range (trapN t), g (((k + 1 : ℕ) : ℝ) * t))
          - (1 / t) * (∫ x in (0 : ℝ)..(trapR t), g x)
          - (1 / 2) * (g (trapR t) - g 0))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  classical
  have hbound :
      ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
        ‖(∑ k ∈ Finset.range (trapN t), g (((k + 1 : ℕ) : ℝ) * t))
            - (1 / t) * (∫ x in (0 : ℝ)..(trapR t), g x)
            - (1 / 2) * (g (trapR t) - g 0)‖
          ≤ ‖firstCellTrapErr g t‖ + M * t := by
    filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))]
      with t ht ht01
    have htpos : 0 < t := ht
    have ht_le_one : t ≤ 1 := le_of_lt ht01
    set N : ℕ := trapN t with hNdef
    have hNpos : 0 < N := by
      have h1le : (1 : ℝ) ≤ 1 / t := by rw [le_div_iff₀ htpos]; simpa using ht_le_one
      have hfloor : 1 ≤ ⌊1 / t⌋₊ := Nat.le_floor (by exact_mod_cast h1le)
      rw [hNdef, trapN]; exact hfloor
    have hNle : (N : ℝ) ≤ 1 / t := by
      rw [hNdef, trapN]; exact Nat.floor_le (by positivity : 0 ≤ 1 / t)
    have hRt_le_one : (N : ℝ) * t ≤ 1 := by
      have hmul := mul_le_mul_of_nonneg_right hNle htpos.le
      have hunit : (1 / t) * t = 1 := by rw [one_div]; exact inv_mul_cancel₀ htpos.ne'
      linarith
    have hRt_le_two : (N : ℝ) * t ≤ 2 := by linarith
    have hIntCells : ∀ k ∈ Finset.range N,
        IntervalIntegrable g MeasureTheory.volume ((k : ℝ) * t) (((k + 1 : ℕ) : ℝ) * t) := by
      intro k hk
      have hkleN_real : ((k + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hk)
      have hright_le_two : (((k + 1 : ℕ) : ℝ) * t) ≤ 2 := by
        have := mul_le_mul_of_nonneg_right hkleN_real htpos.le; linarith
      exact hint (by positivity) hright_le_two
    have hid := trapezoid_sum_identity_range (g := g) (t := t) (N := N) hIntCells
    let F : ℕ → ℝ := fun k =>
      (((g ((k : ℝ) * t) + g (((k + 1 : ℕ) : ℝ) * t)) / 2)
        - (1 / t) * ∫ x in ((k : ℝ) * t)..(((k + 1 : ℕ) : ℝ) * t), g x)
    have hF0 : F 0 = firstCellTrapErr g t := by unfold F firstCellTrapErr; simp
    have hcellRest : ∀ k ∈ (Finset.range N).erase 0, |F k| ≤ M * t ^ 2 := by
      intro k hk
      have hkrange : k ∈ Finset.range N := Finset.mem_of_mem_erase hk
      have hkpos_nat : 0 < k := Nat.pos_of_ne_zero (Finset.mem_erase.mp hk).1
      have hkpos : 0 < (k : ℝ) * t := by positivity
      have hkleN_real : ((k + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hkrange)
      have hright_le_two : (((k + 1 : ℕ) : ℝ) * t) ≤ 2 := by
        have := mul_le_mul_of_nonneg_right hkleN_real htpos.le; linarith
      have haeq : (k : ℝ) * t + t = (((k + 1 : ℕ) : ℝ) * t) := by push_cast; ring
      have hcell := hcell_pos (a := (k : ℝ) * t) (h := t)
        htpos hkpos (by rw [haeq]; exact hright_le_two)
      simpa [F, haeq] using hcell
    rw [trapR, ← hNdef, ← hid, Real.norm_eq_abs]
    have hsplit : (∑ k ∈ Finset.range N, F k)
        = F 0 + ∑ k ∈ (Finset.range N).erase 0, F k := by
      rw [← Finset.add_sum_erase (s := Finset.range N) (a := 0) (f := F)
        (Finset.mem_range.mpr hNpos)]
    rw [show (∑ k ∈ Finset.range N,
        (((g ((k : ℝ) * t) + g (((k + 1 : ℕ) : ℝ) * t)) / 2)
          - (1 / t) * ∫ x in ((k : ℝ) * t)..(((k + 1 : ℕ) : ℝ) * t), g x))
        = ∑ k ∈ Finset.range N, F k from rfl]
    rw [hsplit, hF0]
    calc |firstCellTrapErr g t + ∑ k ∈ (Finset.range N).erase 0, F k|
          ≤ |firstCellTrapErr g t| + |∑ k ∈ (Finset.range N).erase 0, F k| := abs_add_le _ _
      _ ≤ |firstCellTrapErr g t| + ∑ k ∈ (Finset.range N).erase 0, |F k| := by
            linarith [Finset.abs_sum_le_sum_abs F ((Finset.range N).erase 0)]
      _ ≤ |firstCellTrapErr g t| + ∑ _k ∈ (Finset.range N).erase 0, M * t ^ 2 := by
            linarith [Finset.sum_le_sum hcellRest]
      _ = |firstCellTrapErr g t| + ((Finset.range N).erase 0).card * (M * t ^ 2) := by
            simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ |firstCellTrapErr g t| + (N : ℝ) * (M * t ^ 2) := by
            have hcard : (((Finset.range N).erase 0).card : ℝ) ≤ (N : ℝ) := by
              have h := Finset.card_erase_le (s := Finset.range N) (a := 0)
              rw [Finset.card_range] at h; exact_mod_cast h
            have hnon : 0 ≤ M * t ^ 2 := by positivity
            nlinarith
      _ = |firstCellTrapErr g t| + M * ((N : ℝ) * t ^ 2) := by ring
      _ ≤ |firstCellTrapErr g t| + M * t := by
            have hNt2 : (N : ℝ) * t ^ 2 ≤ t := by nlinarith [hRt_le_one, htpos.le]
            have hmul := mul_le_mul_of_nonneg_left hNt2 hM
            linarith
  have hRHS : Tendsto (fun t : ℝ => ‖firstCellTrapErr g t‖ + M * t)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hfirstNorm : Tendsto (fun t : ℝ => ‖firstCellTrapErr g t‖)
        (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_zero_iff_norm_tendsto_zero.mp hfirst
    have hMt : Tendsto (fun t : ℝ => M * t) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have htend : Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
        tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
      simpa using htend.const_mul M
    simpa using hfirstNorm.add hMt
  exact squeeze_zero_norm' hbound hRHS

/-- Open-left head theorem in `Icc 1 (trapN t)` form. -/
theorem trapezoid_head_tendsto_of_cell_bound_pos
    {g : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hint : ∀ ⦃a b : ℝ⦄, 0 ≤ a → b ≤ 2 →
        IntervalIntegrable g MeasureTheory.volume a b)
    (hfirst : Tendsto (firstCellTrapErr g) (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hcell_pos : ∀ ⦃a h : ℝ⦄, 0 < h → 0 < a → a + h ≤ 2 →
        |((g a + g (a + h)) / 2) - (1 / h) * ∫ x in a..(a + h), g x| ≤ M * h ^ 2) :
    Tendsto
      (fun t : ℝ =>
        (∑ k ∈ Finset.Icc 1 (trapN t), g ((k : ℝ) * t))
          - (1 / t) * (∫ x in (0 : ℝ)..(trapR t), g x)
          - (1 / 2) * (g (trapR t) - g 0))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have h := trapezoid_head_range_tendsto_of_cell_bound_pos
    (g := g) (M := M) hM hint hfirst hcell_pos
  refine h.congr' ?_
  filter_upwards with t
  rw [sum_Icc_one_eq_sum_range_succ (fun k : ℕ => g ((k : ℝ) * t)) (trapN t)]

/-- The usable head theorem for `log1mexpReg` (conditional on `[0,b]` integrability). -/
theorem log1mexpReg_head_trapezoid_tendsto_zero
    (hint : ∀ ⦃a b : ℝ⦄, 0 ≤ a → b ≤ 2 →
        IntervalIntegrable log1mexpReg MeasureTheory.volume a b) :
    Tendsto
      (fun t : ℝ =>
        (∑ k ∈ Finset.Icc 1 (trapN t), log1mexpReg ((k : ℝ) * t))
          - (1 / t) * (∫ x in (0 : ℝ)..(trapR t), log1mexpReg x)
          - (1 / 2) * (log1mexpReg (trapR t) - log1mexpReg 0))
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  trapezoid_head_tendsto_of_cell_bound_pos (g := log1mexpReg) (M := (5 : ℝ))
    (by norm_num) hint log1mexpReg_first_cell_tendsto_zero log1mexpReg_cell_trapezoid_bound_pos

end

end AnalyticCombinatorics.Ch8.Partitions
