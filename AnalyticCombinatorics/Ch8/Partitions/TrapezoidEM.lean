import Mathlib

/-!
# Ch8 §VIII — Head trapezoid summation brick (toward the HR constant)

The summation/telescoping core for the singular Euler–Maclaurin route (DOCTRINE
avenue d, brick 2).  It assumes a per-cell trapezoid error bound `|cell| ≤ M·h²`
and concludes the head correction tends to `0` (since `N(t)·M·t² ≤ M·t → 0`).

Architecture (per ChatGPT R3): keep the summation brick generic + robust; prove
the per-cell bound separately from the chosen `C²`/Lipschitz-derivative hypothesis
for `log1mexpReg`.
-/

namespace AnalyticCombinatorics.Ch8.Partitions

open Filter Topology BigOperators
open scoped Topology BigOperators Interval

noncomputable section

/-- Head cutoff `N(t) = ⌊1/t⌋₊`. -/
noncomputable def trapN (t : ℝ) : ℕ := ⌊1 / t⌋₊

/-- Right endpoint `R(t) = N(t)·t`. -/
noncomputable def trapR (t : ℝ) : ℝ := (trapN t : ℝ) * t

/-- Reindex `∑_{k=1}^N f k` as `∑_{k=0}^{N-1} f (k+1)`. -/
lemma sum_Icc_one_eq_sum_range_succ (f : ℕ → ℝ) :
    ∀ N : ℕ, (∑ k ∈ Finset.Icc 1 N, f k) = ∑ k ∈ Finset.range N, f (k + 1) := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ]
      have htop := Finset.sum_Icc_succ_top (a := 1) (b := N) (by omega) f
      rw [htop, ih]

/-- Telescoping shift identity:
`∑_{k<N} f(k+1) - ∑_{k<N} f(k) = f(N) - f(0)`. -/
lemma sum_range_succ_sub_sum_range (f : ℕ → ℝ) :
    ∀ N : ℕ,
      (∑ k ∈ Finset.range N, f (k + 1)) - (∑ k ∈ Finset.range N, f k) = f N - f 0 := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      linarith

/-- Finite exact identity: the right-endpoint sum with endpoint correction equals the
sum of cellwise trapezoid errors (cell `k = [kt, (k+1)t]`). -/
lemma trapezoid_sum_identity_range
    (g : ℝ → ℝ) (t : ℝ) (N : ℕ)
    (hInt : ∀ k ∈ Finset.range N,
        IntervalIntegrable g MeasureTheory.volume
          ((k : ℝ) * t) (((k + 1 : ℕ) : ℝ) * t)) :
    (∑ k ∈ Finset.range N,
        (((g ((k : ℝ) * t) + g (((k + 1 : ℕ) : ℝ) * t)) / 2)
          - (1 / t) * ∫ x in ((k : ℝ) * t)..(((k + 1 : ℕ) : ℝ) * t), g x))
      =
    (∑ k ∈ Finset.range N, g (((k + 1 : ℕ) : ℝ) * t))
      - (1 / t) * (∫ x in (0 : ℝ)..((N : ℝ) * t), g x)
      - (1 / 2) * (g ((N : ℝ) * t) - g 0) := by
  classical
  have hsplit0 :=
    intervalIntegral.sum_integral_adjacent_intervals
      (a := fun k : ℕ => (k : ℝ) * t) (n := N) (f := g)
      (fun k hk => hInt k (Finset.mem_range.mpr hk))
  have hsplit :
      (∑ k ∈ Finset.range N,
          ∫ x in ((k : ℝ) * t)..(((k + 1 : ℕ) : ℝ) * t), g x)
        = ∫ x in (0 : ℝ)..((N : ℝ) * t), g x := by
    simpa using hsplit0
  have hpair :
      (∑ k ∈ Finset.range N,
          (g ((k : ℝ) * t) + g (((k + 1 : ℕ) : ℝ) * t)) / 2)
        = (∑ k ∈ Finset.range N, g (((k + 1 : ℕ) : ℝ) * t))
          - (1 / 2) * (g ((N : ℝ) * t) - g 0) := by
    have hshift := sum_range_succ_sub_sum_range (fun k : ℕ => g ((k : ℝ) * t)) N
    simp only [Nat.cast_zero, zero_mul] at hshift
    have hsplit2 :
        (∑ k ∈ Finset.range N, (g ((k : ℝ) * t) + g (((k + 1 : ℕ) : ℝ) * t)) / 2)
          = ((∑ k ∈ Finset.range N, g ((k : ℝ) * t))
              + (∑ k ∈ Finset.range N, g (((k + 1 : ℕ) : ℝ) * t))) / 2 := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_div]
    rw [hsplit2]
    linarith
  have hintsum :
      (∑ k ∈ Finset.range N,
          (1 / t) * ∫ x in ((k : ℝ) * t)..(((k + 1 : ℕ) : ℝ) * t), g x)
        = (1 / t) * (∫ x in (0 : ℝ)..((N : ℝ) * t), g x) := by
    rw [← Finset.mul_sum, hsplit]
  rw [Finset.sum_sub_distrib, hpair, hintsum]
  ring

/-- Core head trapezoid lemma (range form): given a uniform per-cell trapezoid bound
`|cell| ≤ M·h²` on `[0,2]`, the head correction tends to `0`. -/
theorem trapezoid_head_range_tendsto_of_cell_bound
    {g : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hint : ∀ ⦃a b : ℝ⦄, 0 ≤ a → b ≤ 2 →
          IntervalIntegrable g MeasureTheory.volume a b)
    (hcell : ∀ ⦃a h : ℝ⦄, 0 < h → 0 ≤ a → a + h ≤ 2 →
          |((g a + g (a + h)) / 2) - (1 / h) * ∫ x in a..(a + h), g x| ≤ M * h ^ 2) :
    Tendsto
      (fun t : ℝ =>
        (∑ k ∈ Finset.range (trapN t), g (((k + 1 : ℕ) : ℝ) * t))
          - (1 / t) * (∫ x in (0 : ℝ)..(trapR t), g x)
          - (1 / 2) * (g (trapR t) - g 0))
      (𝓝[>] 0) (𝓝 0) := by
  classical
  have hbound :
      ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
        ‖(∑ k ∈ Finset.range (trapN t), g (((k + 1 : ℕ) : ℝ) * t))
            - (1 / t) * (∫ x in (0 : ℝ)..(trapR t), g x)
            - (1 / 2) * (g (trapR t) - g 0)‖ ≤ M * t := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htpos : 0 < t := ht
    set N : ℕ := trapN t with hNdef
    have hNle : (N : ℝ) ≤ 1 / t := by
      rw [hNdef, trapN]; exact Nat.floor_le (by positivity : 0 ≤ 1 / t)
    have hRt_le_one : (N : ℝ) * t ≤ 1 := by
      have hmul := mul_le_mul_of_nonneg_right hNle htpos.le
      have hunit : (1 / t) * t = 1 := by rw [one_div]; exact inv_mul_cancel₀ htpos.ne'
      linarith
    have hRt_le_two : (N : ℝ) * t ≤ 2 := by linarith
    have hIntCells :
        ∀ k ∈ Finset.range N,
          IntervalIntegrable g MeasureTheory.volume
            ((k : ℝ) * t) (((k + 1 : ℕ) : ℝ) * t) := by
      intro k hk
      have hklt : k < N := Finset.mem_range.mp hk
      have hkleN_real : ((k + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hklt
      have hright_le_two : (((k + 1 : ℕ) : ℝ) * t) ≤ 2 := by
        have := mul_le_mul_of_nonneg_right hkleN_real htpos.le; linarith
      exact hint (by positivity) hright_le_two
    have hid := trapezoid_sum_identity_range (g := g) (t := t) (N := N) hIntCells
    have hcellBound :
        ∀ k ∈ Finset.range N,
          |((g ((k : ℝ) * t) + g (((k + 1 : ℕ) : ℝ) * t)) / 2)
              - (1 / t) * ∫ x in ((k : ℝ) * t)..(((k + 1 : ℕ) : ℝ) * t), g x| ≤ M * t ^ 2 := by
      intro k hk
      have hklt : k < N := Finset.mem_range.mp hk
      have hkleN_real : ((k + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hklt
      have hright_le_two : (((k + 1 : ℕ) : ℝ) * t) ≤ 2 := by
        have := mul_le_mul_of_nonneg_right hkleN_real htpos.le; linarith
      have haeq : (k : ℝ) * t + t = (((k + 1 : ℕ) : ℝ) * t) := by push_cast; ring
      have ha_plus_le_two : (k : ℝ) * t + t ≤ 2 := by rw [haeq]; exact hright_le_two
      have hb := hcell (a := (k : ℝ) * t) (h := t) htpos (by positivity) ha_plus_le_two
      simpa [haeq] using hb
    rw [trapR, ← hNdef, ← hid, Real.norm_eq_abs]
    calc
      |∑ k ∈ Finset.range N,
          (((g ((k : ℝ) * t) + g (((k + 1 : ℕ) : ℝ) * t)) / 2)
            - (1 / t) * ∫ x in ((k : ℝ) * t)..(((k + 1 : ℕ) : ℝ) * t), g x)|
          ≤ ∑ k ∈ Finset.range N,
          |(((g ((k : ℝ) * t) + g (((k + 1 : ℕ) : ℝ) * t)) / 2)
            - (1 / t) * ∫ x in ((k : ℝ) * t)..(((k + 1 : ℕ) : ℝ) * t), g x)| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k ∈ Finset.range N, M * t ^ 2 := Finset.sum_le_sum hcellBound
      _ = (N : ℝ) * (M * t ^ 2) := by simp [Finset.sum_const, nsmul_eq_mul]
      _ = M * ((N : ℝ) * t ^ 2) := by ring
      _ ≤ M * t := by
            have hNt2 : (N : ℝ) * t ^ 2 ≤ t := by nlinarith [hRt_le_one, htpos.le]
            exact mul_le_mul_of_nonneg_left hNt2 hM
  have hMt : Tendsto (fun t : ℝ => M * t) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have htend : Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    simpa using htend.const_mul M
  exact squeeze_zero_norm' hbound hMt

/-- Core head trapezoid lemma (`Icc 1 (N t)` form). -/
theorem trapezoid_head_tendsto_of_cell_bound
    {g : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hint : ∀ ⦃a b : ℝ⦄, 0 ≤ a → b ≤ 2 →
          IntervalIntegrable g MeasureTheory.volume a b)
    (hcell : ∀ ⦃a h : ℝ⦄, 0 < h → 0 ≤ a → a + h ≤ 2 →
          |((g a + g (a + h)) / 2) - (1 / h) * ∫ x in a..(a + h), g x| ≤ M * h ^ 2) :
    Tendsto
      (fun t : ℝ =>
        (∑ k ∈ Finset.Icc 1 (trapN t), g ((k : ℝ) * t))
          - (1 / t) * (∫ x in (0 : ℝ)..(trapR t), g x)
          - (1 / 2) * (g (trapR t) - g 0))
      (𝓝[>] 0) (𝓝 0) := by
  have h := trapezoid_head_range_tendsto_of_cell_bound (g := g) (M := M) hM hint hcell
  refine h.congr' ?_
  filter_upwards with t
  rw [sum_Icc_one_eq_sum_range_succ (fun k : ℕ => g ((k : ℝ) * t)) (trapN t)]

end

end AnalyticCombinatorics.Ch8.Partitions
