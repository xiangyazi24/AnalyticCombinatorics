import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.Tauberian

/-!
# Full logarithmic Tauberian estimates for cumulative coefficients

This file continues the elementary Tauberian argument from `Tauberian.lean`.
-/

open Filter
open scoped BigOperators Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Tauberian

noncomputable section

lemma sqrt_one_add_sub_one_sq_ge_delta_sq_div_sixteen
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    δ ^ 2 / 16 ≤ (Real.sqrt (1 + δ) - 1) ^ 2 := by
  let y : ℝ := Real.sqrt (1 + δ)
  have hc0 : 0 ≤ 1 + δ := by linarith
  have hy_nonneg : 0 ≤ y := by
    dsimp [y]
    exact Real.sqrt_nonneg _
  have hy_sq : y ^ 2 = 1 + δ := by
    dsimp [y]
    exact Real.sq_sqrt hc0
  have hy_ge_one : 1 ≤ y := by
    have hsq : (1 : ℝ) ^ 2 ≤ y ^ 2 := by nlinarith
    exact (sq_le_sq₀ (by norm_num) hy_nonneg).mp hsq
  have hy_le_two : y ≤ 2 := by
    have hsq : y ^ 2 ≤ (2 : ℝ) ^ 2 := by nlinarith
    exact (sq_le_sq₀ hy_nonneg (by norm_num)).mp hsq
  have hδ_eq : δ = (y - 1) * (y + 1) := by nlinarith
  have hδ_le : δ ≤ 4 * (y - 1) := by
    have hy1_nonneg : 0 ≤ y - 1 := by linarith
    nlinarith
  have hbase : δ / 4 ≤ y - 1 := by linarith
  have hbase_nonneg : 0 ≤ δ / 4 := by positivity
  have hy1_nonneg : 0 ≤ y - 1 := by linarith
  have hsquare : (δ / 4) ^ 2 ≤ (y - 1) ^ 2 :=
    (sq_le_sq₀ hbase_nonneg hy1_nonneg).mpr hbase
  have htarget : δ ^ 2 / 16 = (δ / 4) ^ 2 := by ring
  simpa [y, htarget]
    using hsquare

lemma delta_div_four_le_sqrt_one_add_sub_one
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    δ / 4 ≤ Real.sqrt (1 + δ) - 1 := by
  let y : ℝ := Real.sqrt (1 + δ)
  have hc0 : 0 ≤ 1 + δ := by linarith
  have hy_nonneg : 0 ≤ y := by
    dsimp [y]
    exact Real.sqrt_nonneg _
  have hy_sq : y ^ 2 = 1 + δ := by
    dsimp [y]
    exact Real.sq_sqrt hc0
  have hy_ge_one : 1 ≤ y := by
    have hsq : (1 : ℝ) ^ 2 ≤ y ^ 2 := by nlinarith
    exact (sq_le_sq₀ (by norm_num) hy_nonneg).mp hsq
  have hy_le_two : y ≤ 2 := by
    have hsq : y ^ 2 ≤ (2 : ℝ) ^ 2 := by nlinarith
    exact (sq_le_sq₀ hy_nonneg (by norm_num)).mp hsq
  have hδ_eq : δ = (y - 1) * (y + 1) := by nlinarith
  have hδ_le : δ ≤ 4 * (y - 1) := by
    have hy1_nonneg : 0 ≤ y - 1 := by linarith
    nlinarith
  simpa [y] using (show δ / 4 ≤ y - 1 by linarith)

lemma sqrt_one_sub_sub_one_sq_ge_delta_sq_div_sixteen
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    δ ^ 2 / 16 ≤ (Real.sqrt (1 - δ) - 1) ^ 2 := by
  let y : ℝ := Real.sqrt (1 - δ)
  have hc0 : 0 ≤ 1 - δ := by linarith
  have hy_nonneg : 0 ≤ y := by
    dsimp [y]
    exact Real.sqrt_nonneg _
  have hy_sq : y ^ 2 = 1 - δ := by
    dsimp [y]
    exact Real.sq_sqrt hc0
  have hy_le_one : y ≤ 1 := by
    have hsq : y ^ 2 ≤ (1 : ℝ) ^ 2 := by nlinarith
    exact (sq_le_sq₀ hy_nonneg (by norm_num)).mp hsq
  have hδ_eq : δ = (1 - y) * (1 + y) := by nlinarith
  have hδ_le : δ ≤ 4 * (1 - y) := by
    have hy1_nonneg : 0 ≤ 1 - y := by linarith
    nlinarith
  have hbase : δ / 4 ≤ 1 - y := by linarith
  have hbase_nonneg : 0 ≤ δ / 4 := by positivity
  have hy1_nonneg : 0 ≤ 1 - y := by linarith
  have hsquare : (δ / 4) ^ 2 ≤ (1 - y) ^ 2 :=
    (sq_le_sq₀ hbase_nonneg hy1_nonneg).mpr hbase
  have htarget : δ ^ 2 / 16 = (δ / 4) ^ 2 := by ring
  have hsign : (y - 1) ^ 2 = (1 - y) ^ 2 := by ring
  simpa [y, htarget, hsign]
    using hsquare

lemma sqrt_one_add_delta_le_two {δ : ℝ} (hδ1 : δ < 1) :
    Real.sqrt (1 + δ) ≤ 2 := by
  by_cases hc0 : 0 ≤ 1 + δ
  · have hsq : (Real.sqrt (1 + δ)) ^ 2 ≤ (2 : ℝ) ^ 2 := by
      rw [Real.sq_sqrt hc0]
      nlinarith
    exact (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num)).mp hsq
  · have hsqrt_zero : Real.sqrt (1 + δ) = 0 := Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hc0)
    nlinarith

lemma sqrt_one_sub_delta_le_one {δ : ℝ} (hδ0 : 0 < δ) :
    Real.sqrt (1 - δ) ≤ 1 := by
  by_cases hc0 : 0 ≤ 1 - δ
  · have hsq : (Real.sqrt (1 - δ)) ^ 2 ≤ (1 : ℝ) ^ 2 := by
      rw [Real.sq_sqrt hc0]
      nlinarith
    exact (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num)).mp hsq
  · have hsqrt_zero : Real.sqrt (1 - δ) = 0 := Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hc0)
    nlinarith

lemma sqrt_one_add_delta_sub_one_pos {δ : ℝ} (hδ0 : 0 < δ) :
    0 < Real.sqrt (1 + δ) - 1 := by
  have hc0 : 0 ≤ 1 + δ := by linarith
  have hsquare : (1 : ℝ) ^ 2 < (Real.sqrt (1 + δ)) ^ 2 := by
    rw [Real.sq_sqrt hc0]
    nlinarith
  have hlt : (1 : ℝ) < Real.sqrt (1 + δ) :=
    (sq_lt_sq₀ (by norm_num) (Real.sqrt_nonneg _)).mp hsquare
  linarith

lemma sqrt_sub_mul_sqrt_add {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (Real.sqrt x - Real.sqrt y) * (Real.sqrt x + Real.sqrt y) = x - y := by
  calc
    (Real.sqrt x - Real.sqrt y) * (Real.sqrt x + Real.sqrt y)
        = (Real.sqrt x) ^ 2 - (Real.sqrt y) ^ 2 := by ring
    _ = x - y := by rw [Real.sq_sqrt hx, Real.sq_sqrt hy]

lemma exponent_le_boundary_of_le
    {B t M x : ℝ} (ht : 0 < t) (hM : 0 < M)
    (hx0 : 0 ≤ x) (hxM : x ≤ M)
    (hcrit : t * (2 * Real.sqrt M) ≤ B) :
    B * Real.sqrt x - t * x ≤ B * Real.sqrt M - t * M := by
  have hM_nonneg : 0 ≤ M := hM.le
  have hsqrtx_le : Real.sqrt x ≤ Real.sqrt M := Real.sqrt_le_sqrt hxM
  have hsqrt_diff_nonneg : 0 ≤ Real.sqrt M - Real.sqrt x := by linarith
  have hsum_le : Real.sqrt M + Real.sqrt x ≤ 2 * Real.sqrt M := by linarith
  have htsum_le : t * (Real.sqrt M + Real.sqrt x) ≤ t * (2 * Real.sqrt M) :=
    mul_le_mul_of_nonneg_left hsum_le ht.le
  have hfactor : 0 ≤ B - t * (Real.sqrt M + Real.sqrt x) := by linarith
  have hdiff :
      B * Real.sqrt M - t * M - (B * Real.sqrt x - t * x)
        =
      (Real.sqrt M - Real.sqrt x) * (B - t * (Real.sqrt M + Real.sqrt x)) := by
    have hid := sqrt_sub_mul_sqrt_add hM_nonneg hx0
    nlinarith
  have hprod : 0 ≤ (Real.sqrt M - Real.sqrt x) * (B - t * (Real.sqrt M + Real.sqrt x)) :=
    mul_nonneg hsqrt_diff_nonneg hfactor
  nlinarith

lemma sqrt_le_tangent
    {M x : ℝ} (hM : 0 < M) (hxM : M ≤ x) :
    Real.sqrt x ≤ Real.sqrt M + (x - M) / (2 * Real.sqrt M) := by
  have hM_nonneg : 0 ≤ M := hM.le
  have hx_nonneg : 0 ≤ x := hM_nonneg.trans hxM
  have hsqrtM_pos : 0 < Real.sqrt M := Real.sqrt_pos.mpr hM
  have hsqrtM_le : Real.sqrt M ≤ Real.sqrt x := Real.sqrt_le_sqrt hxM
  have hsum_pos : 0 < Real.sqrt x + Real.sqrt M := by positivity
  have hid :
      Real.sqrt x - Real.sqrt M
        = (x - M) / (Real.sqrt x + Real.sqrt M) := by
    field_simp [hsum_pos.ne']
    calc
      (Real.sqrt x - Real.sqrt M) * (Real.sqrt x + Real.sqrt M)
          = (Real.sqrt x) ^ 2 - (Real.sqrt M) ^ 2 := by ring
      _ = x - M := by rw [Real.sq_sqrt hx_nonneg, Real.sq_sqrt hM_nonneg]
  have hden_le : 2 * Real.sqrt M ≤ Real.sqrt x + Real.sqrt M := by
    nlinarith
  have hnum_nonneg : 0 ≤ x - M := by linarith
  have hfrac_le :
      (x - M) / (Real.sqrt x + Real.sqrt M)
        ≤ (x - M) / (2 * Real.sqrt M) := by
    exact div_le_div_of_nonneg_left hnum_nonneg (by positivity) hden_le
  nlinarith

lemma exponent_upper_decay
    {B t M x s : ℝ} (hB : 0 ≤ B) (hM : 0 < M) (hxM : M ≤ x)
    (hs : s * t ≤ t - B / (2 * Real.sqrt M)) :
    B * Real.sqrt x - t * x
      ≤ B * Real.sqrt M - t * M - s * t * (x - M) := by
  have htangent := sqrt_le_tangent hM hxM
  have hdiff_nonneg : 0 ≤ x - M := by linarith
  have hstep :
      B * Real.sqrt x - t * x
        ≤ B * Real.sqrt M - t * M - (t - B / (2 * Real.sqrt M)) * (x - M) := by
    have hB_tangent :
        B * Real.sqrt x
          ≤ B * (Real.sqrt M + (x - M) / (2 * Real.sqrt M)) := by
      exact mul_le_mul_of_nonneg_left htangent hB
    have hsqrtM_pos : 0 < Real.sqrt M := Real.sqrt_pos.mpr hM
    calc
      B * Real.sqrt x - t * x
          ≤ B * (Real.sqrt M + (x - M) / (2 * Real.sqrt M)) - t * x := by
            linarith
      _ = B * Real.sqrt M - t * M - (t - B / (2 * Real.sqrt M)) * (x - M) := by
            field_simp [hsqrtM_pos.ne']
            ring
  have hcoef :
      s * t * (x - M) ≤ (t - B / (2 * Real.sqrt M)) * (x - M) :=
    mul_le_mul_of_nonneg_right hs hdiff_nonneg
  nlinarith

lemma const_le_exp_inv_eventually {D c : ℝ} (hc : 0 < c) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, D ≤ Real.exp (c / t) := by
  let A : ℝ := max (D - 1) 1
  have hApos : 0 < A := by
    dsimp [A]
    exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, t ≤ c / A := by
    have hnhds : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), t ≤ c / A :=
      Iic_mem_nhds (by positivity)
    exact hnhds.filter_mono inf_le_left
  filter_upwards [self_mem_nhdsWithin, hsmall] with t ht ht_small
  have hAle : A ≤ c / t := by
    rw [le_div_iff₀ ht]
    have hmul := mul_le_mul_of_nonneg_left ht_small hApos.le
    have hAc : A * (c / A) = c := by field_simp [hApos.ne']
    nlinarith
  have hDle : D ≤ 1 + c / t := by
    have hDminus : D - 1 ≤ A := by
      dsimp [A]
      exact le_max_left _ _
    linarith
  have hexp : 1 + c / t ≤ Real.exp (c / t) := by
    simpa [add_comm] using Real.add_one_le_exp (c / t)
  exact hDle.trans hexp

lemma inv_sq_linear_absorb_eventually {A c : ℝ} (hA : 0 ≤ A) (hc : 0 < c) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, A / t ^ 2 + 1 ≤ Real.exp (c / t) := by
  let D : ℝ := A * 16 / c ^ 2 + 1
  have hhalf : 0 < c / 2 := by positivity
  have hconst := const_le_exp_inv_eventually (D := D) hhalf
  filter_upwards [self_mem_nhdsWithin, hconst] with t ht hD
  have htpos : 0 < t := ht
  let E : ℝ := Real.exp ((c / 2) / t)
  have hEpos : 0 < E := by
    dsimp [E]
    positivity
  have hEnonneg : 0 ≤ E := hEpos.le
  have hEge_one : 1 ≤ E := by
    have hx0 : 0 ≤ (c / 2) / t := by positivity
    have h := Real.add_one_le_exp ((c / 2) / t)
    dsimp [E]
    linarith
  have hquad0 : 0 ≤ (c / 2) / t := by positivity
  have hquad := exp_quadratic_lower hquad0
  have hquad' : c ^ 2 / (16 * t ^ 2) ≤ E := by
    dsimp [E]
    calc
      c ^ 2 / (16 * t ^ 2) = ((c / 2) / t) ^ 2 / 4 := by
        field_simp [htpos.ne']
        ring
      _ ≤ Real.exp ((c / 2) / t) := hquad
  have hAterm : A / t ^ 2 ≤ (A * 16 / c ^ 2) * E := by
    have hc_sq_pos : 0 < c ^ 2 := sq_pos_of_pos hc
    have ht_sq_pos : 0 < t ^ 2 := sq_pos_of_pos htpos
    have hcoef_nonneg : 0 ≤ A * 16 / c ^ 2 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hquad' hcoef_nonneg
    calc
      A / t ^ 2 = (A * 16 / c ^ 2) * (c ^ 2 / (16 * t ^ 2)) := by
        field_simp [hc.ne', htpos.ne']
      _ ≤ (A * 16 / c ^ 2) * E := hmul
  have hsum : A / t ^ 2 + 1 ≤ D * E := by
    dsimp [D]
    nlinarith
  have hprod : D * E ≤ E * E := by
    exact mul_le_mul_of_nonneg_right hD hEnonneg
  calc
    A / t ^ 2 + 1 ≤ D * E := hsum
    _ ≤ E * E := hprod
    _ = Real.exp (c / t) := by
      dsimp [E]
      rw [← Real.exp_add]
      congr 1
      field_simp [htpos.ne']
      ring

lemma lower_indicator_tsum_le_count {L C : ℝ} (hL : 0 ≤ L) (hC : 0 ≤ C) :
    (∑' N : ℕ, if (N : ℝ) ≤ L then C else 0)
      ≤ ((Nat.floor L : ℝ) + 1) * C := by
  let f : ℕ → ℝ := fun N => if (N : ℝ) ≤ L then C else 0
  have hzero : ∀ N ∉ Finset.range (Nat.floor L + 1), f N = 0 := by
    intro N hN
    have hnotlt : ¬N < Nat.floor L + 1 := by
      simpa [Finset.mem_range] using hN
    have hge : Nat.floor L + 1 ≤ N := Nat.le_of_not_lt hnotlt
    have hfloor_lt : Nat.floor L < N := Nat.lt_of_succ_le hge
    have hLlt : L < (N : ℝ) := (Nat.floor_lt hL).mp hfloor_lt
    dsimp [f]
    simp [not_le.mpr hLlt]
  calc
    (∑' N : ℕ, if (N : ℝ) ≤ L then C else 0)
        = ∑ N ∈ Finset.range (Nat.floor L + 1), f N := by
          exact tsum_eq_sum hzero
    _ ≤ ∑ _N ∈ Finset.range (Nat.floor L + 1), C := by
          exact Finset.sum_le_sum fun N _ => by
            dsimp [f]
            split
            · rfl
            · exact hC
    _ = ((Nat.floor L : ℝ) + 1) * C := by
          simp [Finset.sum_const, Nat.cast_add, Nat.cast_one, mul_comm]

lemma boundary_exponent_eq
    {K c α t : ℝ} (hK : 0 ≤ K) (hc : 0 ≤ c) (ht : 0 < t) :
    ((2 + α) * Real.sqrt K) * Real.sqrt (c * K / t ^ 2)
        - t * (c * K / t ^ 2)
      =
    (K / t) * ((2 + α) * Real.sqrt c - c) := by
  have ht_ne : t ≠ 0 := ht.ne'
  have hsqrt :
      Real.sqrt (c * K / t ^ 2) = Real.sqrt c * Real.sqrt K / t := by
    rw [Real.sqrt_div (mul_nonneg hc hK)]
    rw [Real.sqrt_mul hc]
    rw [Real.sqrt_sq ht.le]
  have hsqrtK_sq : (Real.sqrt K) ^ 2 = K := Real.sq_sqrt hK
  rw [hsqrt]
  field_simp [ht_ne]
  ring_nf
  rw [hsqrtK_sq]
  ring

lemma sqrt_mul_div_sq_eq
    {K c t : ℝ} (hK : 0 ≤ K) (hc : 0 ≤ c) (ht : 0 < t) :
    Real.sqrt (c * K / t ^ 2) = Real.sqrt c * Real.sqrt K / t := by
  rw [Real.sqrt_div (mul_nonneg hc hK)]
  rw [Real.sqrt_mul hc]
  rw [Real.sqrt_sq ht.le]

lemma lower_boundary_coef_le
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (2 + δ ^ 2 / 64) * Real.sqrt (1 - δ) - (1 - δ)
      ≤ 1 - δ ^ 2 / 32 := by
  let y : ℝ := Real.sqrt (1 - δ)
  have hy_nonneg : 0 ≤ y := by
    dsimp [y]
    exact Real.sqrt_nonneg _
  have hc0 : 0 ≤ 1 - δ := by linarith
  have hy_sq : y ^ 2 = 1 - δ := by
    dsimp [y]
    exact Real.sq_sqrt hc0
  have hy_le_one : y ≤ 1 := by simpa [y] using sqrt_one_sub_delta_le_one hδ0
  have hmargin : δ ^ 2 / 16 ≤ (y - 1) ^ 2 := by
    simpa [y] using sqrt_one_sub_sub_one_sq_ge_delta_sq_div_sixteen hδ0 hδ1
  have hδsq_nonneg : 0 ≤ δ ^ 2 := sq_nonneg δ
  have hsmall : δ ^ 2 / 64 * y ≤ δ ^ 2 / 64 := by
    nlinarith
  have hbase : 2 * y - y ^ 2 ≤ 1 - δ ^ 2 / 16 := by
    nlinarith
  have hcalc :
      (2 + δ ^ 2 / 64) * y - y ^ 2
        ≤ 1 - δ ^ 2 / 32 := by
    nlinarith
  calc
    (2 + δ ^ 2 / 64) * Real.sqrt (1 - δ) - (1 - δ)
        = (2 + δ ^ 2 / 64) * y - y ^ 2 := by
          dsimp [y]
          rw [hy_sq]
    _ ≤ 1 - δ ^ 2 / 32 := hcalc

lemma upper_boundary_coef_le
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (2 + δ ^ 2 / 64) * Real.sqrt (1 + δ) - (1 + δ)
      ≤ 1 - δ ^ 2 / 32 := by
  let y : ℝ := Real.sqrt (1 + δ)
  have hy_nonneg : 0 ≤ y := by
    dsimp [y]
    exact Real.sqrt_nonneg _
  have hc0 : 0 ≤ 1 + δ := by linarith
  have hy_sq : y ^ 2 = 1 + δ := by
    dsimp [y]
    exact Real.sq_sqrt hc0
  have hy_le_two : y ≤ 2 := by simpa [y] using sqrt_one_add_delta_le_two hδ1
  have hmargin : δ ^ 2 / 16 ≤ (y - 1) ^ 2 := by
    simpa [y] using sqrt_one_add_sub_one_sq_ge_delta_sq_div_sixteen hδ0 hδ1
  have hδsq_nonneg : 0 ≤ δ ^ 2 := sq_nonneg δ
  have hsmall : δ ^ 2 / 64 * y ≤ δ ^ 2 / 32 := by
    nlinarith
  have hbase : 2 * y - y ^ 2 ≤ 1 - δ ^ 2 / 16 := by
    nlinarith
  have hcalc :
      (2 + δ ^ 2 / 64) * y - y ^ 2
        ≤ 1 - δ ^ 2 / 32 := by
    nlinarith
  simpa [y, hy_sq, mul_add, add_mul, sub_eq_add_neg] using hcalc

lemma lower_boundary_exponent_le
    {K δ t : ℝ} (hK : 0 < K) (hδ0 : 0 < δ) (hδ1 : δ < 1) (ht : 0 < t) :
    (2 * Real.sqrt K + Real.sqrt K * (δ ^ 2 / 64))
        * Real.sqrt ((1 - δ) * K / t ^ 2)
        - t * ((1 - δ) * K / t ^ 2)
      ≤ (K - K * δ ^ 2 / 32) / t := by
  have hc : 0 ≤ 1 - δ := by linarith
  have hB :
      2 * Real.sqrt K + Real.sqrt K * (δ ^ 2 / 64)
        = (2 + δ ^ 2 / 64) * Real.sqrt K := by ring
  have heq := boundary_exponent_eq (K := K) (c := 1 - δ)
    (α := δ ^ 2 / 64) (t := t) hK.le hc ht
  have hcoef := lower_boundary_coef_le hδ0 hδ1
  calc
    (2 * Real.sqrt K + Real.sqrt K * (δ ^ 2 / 64))
        * Real.sqrt ((1 - δ) * K / t ^ 2)
        - t * ((1 - δ) * K / t ^ 2)
        = (K / t) *
            ((2 + δ ^ 2 / 64) * Real.sqrt (1 - δ) - (1 - δ)) := by
          rw [hB, heq]
    _ ≤ (K / t) * (1 - δ ^ 2 / 32) := by
          exact mul_le_mul_of_nonneg_left hcoef (div_nonneg hK.le ht.le)
    _ = (K - K * δ ^ 2 / 32) / t := by
          field_simp [ht.ne']

lemma upper_boundary_exponent_le
    {K δ t : ℝ} (hK : 0 < K) (hδ0 : 0 < δ) (hδ1 : δ < 1) (ht : 0 < t) :
    (2 * Real.sqrt K + Real.sqrt K * (δ ^ 2 / 64))
        * Real.sqrt ((1 + δ) * K / t ^ 2)
        - t * ((1 + δ) * K / t ^ 2)
      ≤ (K - K * δ ^ 2 / 32) / t := by
  have hc : 0 ≤ 1 + δ := by linarith
  have hB :
      2 * Real.sqrt K + Real.sqrt K * (δ ^ 2 / 64)
        = (2 + δ ^ 2 / 64) * Real.sqrt K := by ring
  have heq := boundary_exponent_eq (K := K) (c := 1 + δ)
    (α := δ ^ 2 / 64) (t := t) hK.le hc ht
  have hcoef := upper_boundary_coef_le hδ0 hδ1
  calc
    (2 * Real.sqrt K + Real.sqrt K * (δ ^ 2 / 64))
        * Real.sqrt ((1 + δ) * K / t ^ 2)
        - t * ((1 + δ) * K / t ^ 2)
        = (K / t) *
            ((2 + δ ^ 2 / 64) * Real.sqrt (1 + δ) - (1 + δ)) := by
          rw [hB, heq]
    _ ≤ (K / t) * (1 - δ ^ 2 / 32) := by
          exact mul_le_mul_of_nonneg_left hcoef (div_nonneg hK.le ht.le)
    _ = (K - K * δ ^ 2 / 32) / t := by
          field_simp [ht.ne']

lemma strong_gap_s_pos {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    0 < 1 - (1 + δ ^ 2 / 128) / Real.sqrt (1 + δ) := by
  have hypos : 0 < Real.sqrt (1 + δ) := by positivity
  have hgap := delta_div_four_le_sqrt_one_add_sub_one hδ0 hδ1
  have halpha_lt : δ ^ 2 / 128 < δ / 4 := by nlinarith [hδ0, hδ1]
  have hnum_lt : 1 + δ ^ 2 / 128 < Real.sqrt (1 + δ) := by linarith
  have hfrac_lt : (1 + δ ^ 2 / 128) / Real.sqrt (1 + δ) < 1 := by
    exact (div_lt_one hypos).mpr hnum_lt
  linarith

lemma lower_tail_tsum_bound
    {K δ t : ℝ} (hK : 0 < K) (hδ0 : 0 < δ) (hδ1 : δ < 1) (ht : 0 < t) :
    (∑' N : ℕ,
      if (N : ℝ) ≤ (1 - δ) * K / t ^ 2 then
        Real.exp
          ((2 * Real.sqrt K + Real.sqrt K * (δ ^ 2 / 64)) * Real.sqrt (N : ℝ)
            - t * N)
      else 0)
      ≤
    ((Nat.floor ((1 - δ) * K / t ^ 2) : ℝ) + 1)
      * Real.exp ((K - K * δ ^ 2 / 32) / t) := by
  let L : ℝ := (1 - δ) * K / t ^ 2
  let B : ℝ := 2 * Real.sqrt K + Real.sqrt K * (δ ^ 2 / 64)
  let C : ℝ := Real.exp ((K - K * δ ^ 2 / 32) / t)
  have hLpos : 0 < L := by
    dsimp [L]
    exact div_pos (mul_pos (by linarith) hK) (sq_pos_of_pos ht)
  have hL_nonneg : 0 ≤ L := hLpos.le
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  have hcrit : t * (2 * Real.sqrt L) ≤ B := by
    have hsqrtL := sqrt_mul_div_sq_eq (K := K) (c := 1 - δ) (t := t)
      hK.le (by linarith) ht
    have hsqrt_le_one : Real.sqrt (1 - δ) ≤ 1 := sqrt_one_sub_delta_le_one hδ0
    have hsqrtK_nonneg : 0 ≤ Real.sqrt K := Real.sqrt_nonneg _
    dsimp [L, B] at hsqrtL ⊢
    rw [hsqrtL]
    field_simp [ht.ne']
    nlinarith [mul_le_mul_of_nonneg_right hsqrt_le_one hsqrtK_nonneg,
      sq_nonneg δ]
  have hboundary := lower_boundary_exponent_le hK hδ0 hδ1 ht
  let f : ℕ → ℝ := fun N =>
    if (N : ℝ) ≤ L then
      Real.exp (B * Real.sqrt (N : ℝ) - t * N)
    else 0
  have hzero : ∀ N ∉ Finset.range (Nat.floor L + 1), f N = 0 := by
    intro N hN
    have hnotlt : ¬N < Nat.floor L + 1 := by
      simpa [Finset.mem_range] using hN
    have hge : Nat.floor L + 1 ≤ N := Nat.le_of_not_lt hnotlt
    have hfloor_lt : Nat.floor L < N := Nat.lt_of_succ_le hge
    have hLlt : L < (N : ℝ) := (Nat.floor_lt hL_nonneg).mp hfloor_lt
    dsimp [f]
    simp [not_le.mpr hLlt]
  have hpoint :
      ∀ N ∈ Finset.range (Nat.floor L + 1), f N ≤ C := by
    intro N _hN
    dsimp [f]
    split_ifs with hNL
    · have hmono := exponent_le_boundary_of_le (B := B) (t := t) (M := L) (x := (N : ℝ))
        ht hLpos (by positivity) hNL hcrit
      have hbd :
          B * Real.sqrt L - t * L ≤ (K - K * δ ^ 2 / 32) / t := by
        dsimp [B, L]
        simpa [mul_comm, mul_left_comm, mul_assoc] using hboundary
      exact Real.exp_monotone (hmono.trans hbd)
    · dsimp [C]
      positivity
  calc
    (∑' N : ℕ,
      if (N : ℝ) ≤ (1 - δ) * K / t ^ 2 then
        Real.exp
          ((2 * Real.sqrt K + Real.sqrt K * (δ ^ 2 / 64)) * Real.sqrt (N : ℝ)
            - t * N)
      else 0)
        = ∑' N : ℕ, f N := by
          apply tsum_congr
          intro N
          simp [f, L, B]
    _ = ∑ N ∈ Finset.range (Nat.floor L + 1), f N := by
          exact tsum_eq_sum hzero
    _ ≤ ∑ _N ∈ Finset.range (Nat.floor L + 1), C := by
          exact Finset.sum_le_sum hpoint
    _ = ((Nat.floor L : ℝ) + 1) * C := by
          simp [Finset.sum_const, Nat.cast_add, Nat.cast_one]
    _ =
      ((Nat.floor ((1 - δ) * K / t ^ 2) : ℝ) + 1)
        * Real.exp ((K - K * δ ^ 2 / 32) / t) := by
          rfl

lemma upper_tail_tsum_bound
    {K δ t : ℝ} (hK : 0 < K) (hδ0 : 0 < δ) (hδ1 : δ < 1) (ht : 0 < t) :
    let s : ℝ := 1 - (1 + δ ^ 2 / 128) / Real.sqrt (1 + δ)
    (∑' N : ℕ,
      if (1 + δ) * K / t ^ 2 ≤ (N : ℝ) then
        Real.exp
          ((2 * Real.sqrt K + Real.sqrt K * (δ ^ 2 / 64)) * Real.sqrt (N : ℝ)
            - t * N)
      else 0)
      ≤
    Real.exp ((K - K * δ ^ 2 / 32) / t)
      * (1 - Real.exp (-(s * t)))⁻¹ := by
  intro s
  let U : ℝ := (1 + δ) * K / t ^ 2
  let B : ℝ := 2 * Real.sqrt K + Real.sqrt K * (δ ^ 2 / 64)
  let C : ℝ := Real.exp ((K - K * δ ^ 2 / 32) / t)
  let n0 : ℕ := Nat.ceil U
  let u : ℕ → ℝ := fun N =>
    if U ≤ (N : ℝ) then Real.exp (B * Real.sqrt (N : ℝ) - t * N) else 0
  have hUpos : 0 < U := by
    dsimp [U]
    exact div_pos (mul_pos (by linarith) hK) (sq_pos_of_pos ht)
  have hU_nonneg : 0 ≤ U := hUpos.le
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  have hs_pos : 0 < s := by
    dsimp [s]
    exact strong_gap_s_pos hδ0 hδ1
  have hst_pos : 0 < s * t := mul_pos hs_pos ht
  have hslope : s * t ≤ t - B / (2 * Real.sqrt U) := by
    have hsqrtU := sqrt_mul_div_sq_eq (K := K) (c := 1 + δ) (t := t)
      hK.le (by linarith) ht
    have hsqrtK_pos : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK
    have hsqrtc_pos : 0 < Real.sqrt (1 + δ) := by positivity
    dsimp [s, U, B] at hsqrtU ⊢
    rw [hsqrtU]
    field_simp [ht.ne', hsqrtK_pos.ne', hsqrtc_pos.ne']
    ring_nf
    linarith
  have hboundary := upper_boundary_exponent_le hK hδ0 hδ1 ht
  have hu_nonneg : ∀ N, 0 ≤ u N := by
    intro N
    dsimp [u]
    split <;> positivity
  have hu_le_full :
      ∀ N, u N ≤ Real.exp (B * Real.sqrt (N : ℝ) - t * N) := by
    intro N
    dsimp [u]
    split
    · rfl
    · positivity
  have hfull_summable :
      Summable fun N : ℕ => Real.exp (B * Real.sqrt (N : ℝ) - t * N) :=
    exp_sqrt_sub_linear_summable ht
  have hu_summable : Summable u :=
    hfull_summable.of_nonneg_of_le hu_nonneg hu_le_full
  have hrange_zero : ∑ N ∈ Finset.range n0, u N = 0 := by
    refine Finset.sum_eq_zero ?_
    intro N hN
    have hNlt : N < n0 := Finset.mem_range.mp hN
    have hnot : ¬ U ≤ (N : ℝ) := by
      intro hUN
      have hn0le : n0 ≤ N := (Nat.ceil_le).mpr hUN
      omega
    dsimp [u]
    simp [hnot]
  have hsplit := Summable.sum_add_tsum_nat_add n0 hu_summable
  have htail_eq :
      (∑' k : ℕ, u (k + n0)) = ∑' N : ℕ, u N := by
    simpa [hrange_zero] using hsplit
  have htail_point :
      ∀ k : ℕ,
        u (k + n0) ≤ C * Real.exp (-(s * t) * k) := by
    intro k
    have hceil : U ≤ (n0 : ℝ) := Nat.le_ceil U
    have hNgeU : U ≤ ((k + n0 : ℕ) : ℝ) := by
      exact hceil.trans (by exact_mod_cast Nat.le_add_left n0 k)
    have hdist : (k : ℝ) ≤ ((k + n0 : ℕ) : ℝ) - U := by
      have hcast : ((k + n0 : ℕ) : ℝ) = (k : ℝ) + (n0 : ℝ) := by norm_num
      rw [hcast]
      nlinarith
    have hdecay := exponent_upper_decay (B := B) (t := t) (M := U)
      (x := ((k + n0 : ℕ) : ℝ)) (s := s) hB_nonneg hUpos hNgeU hslope
    have hbd :
        B * Real.sqrt U - t * U ≤ (K - K * δ ^ 2 / 32) / t := by
      dsimp [B, U]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hboundary
    have hdist_decay :
        -(s * t) * (((k + n0 : ℕ) : ℝ) - U) ≤ -(s * t) * (k : ℝ) := by
      exact mul_le_mul_of_nonpos_left hdist (by nlinarith [hst_pos])
    have hexp_arg :
        B * Real.sqrt (((k + n0 : ℕ) : ℝ)) - t * ((k + n0 : ℕ) : ℝ)
          ≤ (K - K * δ ^ 2 / 32) / t - s * t * (k : ℝ) := by
      nlinarith
    calc
      u (k + n0)
          = Real.exp
            (B * Real.sqrt (((k + n0 : ℕ) : ℝ)) - t * ((k + n0 : ℕ) : ℝ)) := by
              dsimp [u]
              rw [if_pos hNgeU]
      _ ≤ Real.exp ((K - K * δ ^ 2 / 32) / t - s * t * (k : ℝ)) :=
            Real.exp_monotone hexp_arg
      _ = C * Real.exp (-(s * t) * k) := by
            dsimp [C]
            rw [← Real.exp_add]
            congr 1
            ring
  have hgeom_summable : Summable fun k : ℕ => C * Real.exp (-(s * t) * k) := by
    have hgeom : Summable fun k : ℕ => Real.exp (-(s * t) * k) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (Real.summable_exp_nat_mul_iff.mpr (by nlinarith [hst_pos] : -(s * t) < 0))
    exact hgeom.mul_left C
  have htail_summable : Summable fun k : ℕ => u (k + n0) := by
    exact (summable_nat_add_iff n0).2 hu_summable
  have htail_le :
      (∑' k : ℕ, u (k + n0)) ≤ ∑' k : ℕ, C * Real.exp (-(s * t) * k) :=
    htail_summable.tsum_le_tsum htail_point hgeom_summable
  calc
    (∑' N : ℕ,
      if (1 + δ) * K / t ^ 2 ≤ (N : ℝ) then
        Real.exp
          ((2 * Real.sqrt K + Real.sqrt K * (δ ^ 2 / 64)) * Real.sqrt (N : ℝ)
            - t * N)
      else 0)
        = ∑' N : ℕ, u N := by
          apply tsum_congr
          intro N
          simp [u, U, B]
    _ = ∑' k : ℕ, u (k + n0) := htail_eq.symm
    _ ≤ ∑' k : ℕ, C * Real.exp (-(s * t) * k) := htail_le
    _ = C * (1 - Real.exp (-(s * t)))⁻¹ := by
          rw [tsum_mul_left]
          rw [tsum_exp_neg_mul_nat hst_pos]
    _ =
      Real.exp ((K - K * δ ^ 2 / 32) / t)
        * (1 - Real.exp (-(s * t)))⁻¹ := by
          rfl

theorem sqrt_laplace_restricted_gap_strong
    {K δ : ℝ} (hK : 0 < K) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ η ρ : ℝ, 0 < η ∧ 0 < ρ ∧ ∀ᶠ t in 𝓝[>] 0,
      (∑' N : ℕ,
        if (1 - δ) * K / t ^ 2 ≤ (N : ℝ)
            ∧ (N : ℝ) ≤ (1 + δ) * K / t ^ 2 then 0
        else Real.exp ((2 * Real.sqrt K + η) * Real.sqrt (N : ℝ) - t * N))
        ≤ Real.exp ((K - ρ) / t) := by
  let η : ℝ := Real.sqrt K * (δ ^ 2 / 64)
  let R : ℝ := K * δ ^ 2 / 32
  let ρ : ℝ := R / 2
  have hη : 0 < η := by
    dsimp [η]
    positivity
  have hRpos : 0 < R := by
    dsimp [R]
    positivity
  have hρ : 0 < ρ := by
    dsimp [ρ]
    positivity
  refine ⟨η, ρ, hη, hρ, ?_⟩
  let s : ℝ := 1 - (1 + δ ^ 2 / 128) / Real.sqrt (1 + δ)
  have hs_pos : 0 < s := by
    dsimp [s]
    exact strong_gap_s_pos hδ hδ1
  have hquarter : 0 < R / 4 := by positivity
  have hpolyEv := inv_sq_linear_absorb_eventually (A := K) (c := R / 4) hK.le hquarter
  have hgeomEv := geom_inv_le_exp_eventually hs_pos hquarter
  have htwoEv := const_le_exp_inv_eventually (D := (2 : ℝ)) hquarter
  filter_upwards [self_mem_nhdsWithin, hpolyEv, hgeomEv, htwoEv] with t ht hpoly hgeom htwo
  have htpos : 0 < t := ht
  let L : ℝ := (1 - δ) * K / t ^ 2
  let U : ℝ := (1 + δ) * K / t ^ 2
  let B : ℝ := 2 * Real.sqrt K + η
  let B0 : ℝ := 2 * Real.sqrt K + Real.sqrt K * (δ ^ 2 / 64)
  let C0 : ℝ := Real.exp ((K - R) / t)
  have hB_eq : B = B0 := by
    dsimp [B, B0, η]
  have hB0_nonneg : 0 ≤ B0 := by
    dsimp [B0]
    positivity
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    exact div_nonneg (mul_nonneg (by linarith : 0 ≤ 1 - δ) hK.le) (sq_nonneg t)
  have hU_nonneg : 0 ≤ U := by
    dsimp [U]
    exact div_nonneg (mul_nonneg (by linarith : 0 ≤ 1 + δ) hK.le) (sq_nonneg t)
  let rterm : ℕ → ℝ := fun N =>
    if L ≤ (N : ℝ) ∧ (N : ℝ) ≤ U then 0
    else Real.exp (B * Real.sqrt (N : ℝ) - t * N)
  let lterm : ℕ → ℝ := fun N =>
    if (N : ℝ) ≤ L then Real.exp (B0 * Real.sqrt (N : ℝ) - t * N) else 0
  let uterm : ℕ → ℝ := fun N =>
    if U ≤ (N : ℝ) then Real.exp (B0 * Real.sqrt (N : ℝ) - t * N) else 0
  have hpoint : ∀ N, rterm N ≤ lterm N + uterm N := by
    intro N
    dsimp [rterm, lterm, uterm]
    by_cases hwin : L ≤ (N : ℝ) ∧ (N : ℝ) ≤ U
    · simp [hwin]
      positivity
    · rw [if_neg hwin]
      by_cases hNL : (N : ℝ) ≤ L
      · rw [if_pos hNL]
        have hBsubst :
            Real.exp (B * Real.sqrt (N : ℝ) - t * N)
              = Real.exp (B0 * Real.sqrt (N : ℝ) - t * N) := by
          rw [hB_eq]
        rw [hBsubst]
        by_cases hUN : U ≤ (N : ℝ)
        · rw [if_pos hUN]
          linarith [Real.exp_pos (B0 * Real.sqrt (N : ℝ) - t * N)]
        · rw [if_neg hUN]
          linarith
      · have hLN : L ≤ (N : ℝ) := le_of_lt (lt_of_not_ge hNL)
        have hnotNU : ¬ (N : ℝ) ≤ U := by
          intro hNU
          exact hwin ⟨hLN, hNU⟩
        have hUN : U ≤ (N : ℝ) := le_of_lt (lt_of_not_ge hnotNU)
        rw [if_neg hNL, if_pos hUN]
        have hBsubst :
            Real.exp (B * Real.sqrt (N : ℝ) - t * N)
              = Real.exp (B0 * Real.sqrt (N : ℝ) - t * N) := by
          rw [hB_eq]
        rw [hBsubst]
        linarith
  have hfull_summable :
      Summable fun N : ℕ => Real.exp (B0 * Real.sqrt (N : ℝ) - t * N) :=
    exp_sqrt_sub_linear_summable htpos
  have hl_nonneg : ∀ N, 0 ≤ lterm N := by
    intro N
    dsimp [lterm]
    split <;> positivity
  have hu_nonneg : ∀ N, 0 ≤ uterm N := by
    intro N
    dsimp [uterm]
    split <;> positivity
  have hr_nonneg : ∀ N, 0 ≤ rterm N := by
    intro N
    dsimp [rterm]
    split <;> positivity
  have hl_le_full :
      ∀ N, lterm N ≤ Real.exp (B0 * Real.sqrt (N : ℝ) - t * N) := by
    intro N
    dsimp [lterm]
    split
    · rfl
    · positivity
  have hu_le_full :
      ∀ N, uterm N ≤ Real.exp (B0 * Real.sqrt (N : ℝ) - t * N) := by
    intro N
    dsimp [uterm]
    split
    · rfl
    · positivity
  have hr_le_full :
      ∀ N, rterm N ≤ Real.exp (B0 * Real.sqrt (N : ℝ) - t * N) := by
    intro N
    dsimp [rterm]
    split
    · positivity
    · rw [hB_eq]
  have hl_summable : Summable lterm :=
    hfull_summable.of_nonneg_of_le hl_nonneg hl_le_full
  have hu_summable : Summable uterm :=
    hfull_summable.of_nonneg_of_le hu_nonneg hu_le_full
  have hr_summable : Summable rterm :=
    hfull_summable.of_nonneg_of_le hr_nonneg hr_le_full
  have hsplit :
      (∑' N : ℕ, rterm N) ≤ (∑' N : ℕ, lterm N) + (∑' N : ℕ, uterm N) := by
    calc
      (∑' N : ℕ, rterm N)
          ≤ ∑' N : ℕ, (lterm N + uterm N) :=
            hr_summable.tsum_le_tsum hpoint (hl_summable.add hu_summable)
      _ = (∑' N : ℕ, lterm N) + (∑' N : ℕ, uterm N) :=
            (hl_summable.tsum_add hu_summable)
  have hlower_raw := lower_tail_tsum_bound hK hδ hδ1 htpos
  have hupper_raw := upper_tail_tsum_bound hK hδ hδ1 htpos
  have hcount_le : ((Nat.floor L : ℝ) + 1) ≤ K / t ^ 2 + 1 := by
    have hfloor_le : (Nat.floor L : ℝ) ≤ L := Nat.floor_le hL_nonneg
    have hL_le : L ≤ K / t ^ 2 := by
      dsimp [L]
      have hden_nonneg : 0 ≤ K / t ^ 2 := by positivity
      have hmul := mul_le_mul_of_nonneg_right (by linarith : 1 - δ ≤ 1) hden_nonneg
      calc
        (1 - δ) * K / t ^ 2 = (1 - δ) * (K / t ^ 2) := by ring
        _ ≤ 1 * (K / t ^ 2) := hmul
        _ = K / t ^ 2 := by ring
    linarith
  have hcount_exp : ((Nat.floor L : ℝ) + 1) ≤ Real.exp ((R / 4) / t) :=
    hcount_le.trans hpoly
  have hlower :
      (∑' N : ℕ, lterm N) ≤ Real.exp ((K - 3 * R / 4) / t) := by
    have hraw :
        (∑' N : ℕ, lterm N)
          ≤ ((Nat.floor L : ℝ) + 1) * C0 := by
      dsimp [lterm, L, B0, C0]
      simpa [R, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
        using hlower_raw
    calc
      (∑' N : ℕ, lterm N)
          ≤ ((Nat.floor L : ℝ) + 1) * C0 := hraw
      _ ≤ Real.exp ((R / 4) / t) * C0 := by
            exact mul_le_mul_of_nonneg_right hcount_exp (by positivity)
      _ = Real.exp ((K - 3 * R / 4) / t) := by
            dsimp [C0]
            rw [← Real.exp_add]
            congr 1
            field_simp [htpos.ne']
            ring
  have hupper :
      (∑' N : ℕ, uterm N) ≤ Real.exp ((K - 3 * R / 4) / t) := by
    have hraw :
        (∑' N : ℕ, uterm N)
          ≤ C0 * (1 - Real.exp (-(s * t)))⁻¹ := by
      dsimp [uterm, U, B0, C0, s]
      simpa [R, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
        using hupper_raw
    calc
      (∑' N : ℕ, uterm N)
          ≤ C0 * (1 - Real.exp (-(s * t)))⁻¹ := hraw
      _ ≤ C0 * Real.exp ((R / 4) / t) := by
            exact mul_le_mul_of_nonneg_left hgeom (by positivity)
      _ = Real.exp ((K - 3 * R / 4) / t) := by
            dsimp [C0]
            rw [← Real.exp_add]
            congr 1
            field_simp [htpos.ne']
            ring
  have hsum_two :
      (∑' N : ℕ, rterm N) ≤ 2 * Real.exp ((K - 3 * R / 4) / t) := by
    linarith
  have htwo_absorb :
      2 * Real.exp ((K - 3 * R / 4) / t)
        ≤ Real.exp ((K - R / 2) / t) := by
    calc
      2 * Real.exp ((K - 3 * R / 4) / t)
          ≤ Real.exp ((R / 4) / t) * Real.exp ((K - 3 * R / 4) / t) := by
            exact mul_le_mul_of_nonneg_right htwo (by positivity)
      _ = Real.exp ((K - R / 2) / t) := by
            rw [← Real.exp_add]
            congr 1
            field_simp [htpos.ne']
            ring
  calc
    (∑' N : ℕ,
        if (1 - δ) * K / t ^ 2 ≤ (N : ℝ)
            ∧ (N : ℝ) ≤ (1 + δ) * K / t ^ 2 then 0
        else Real.exp ((2 * Real.sqrt K + η) * Real.sqrt (N : ℝ) - t * N))
        = ∑' N : ℕ, rterm N := by
          apply tsum_congr
          intro N
          simp [rterm, L, U, B]
    _ ≤ 2 * Real.exp ((K - 3 * R / 4) / t) := hsum_two
    _ ≤ Real.exp ((K - R / 2) / t) := htwo_absorb
    _ = Real.exp ((K - ρ) / t) := by
          dsimp [ρ]

end

end AnalyticCombinatorics.Ch8.Partitions.Tauberian
