import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass
import AnalyticCombinatorics.PartA.Ch2.LabelledClass
import AnalyticCombinatorics.Examples.Compositions
import Mathlib.Combinatorics.Enumerative.Bell

open PowerSeries CombinatorialClass Finset
open scoped PowerSeries.WithPiTopology

/-- The EGF whose coefficients are Mathlib's Bell numbers. -/
noncomputable def bellSeries : PowerSeries ℚ :=
  PowerSeries.mk fun n => (Nat.bell n : ℚ) / n.factorial

/-- The EGF formed from labelled SET counts. -/
noncomputable def labelSetSeries (B : CombinatorialClass) : PowerSeries ℚ :=
  PowerSeries.mk fun n => CombinatorialClass.labelSetCount B n / n.factorial

/-- The finite partial exponential series visible at coefficient level `n`. -/
noncomputable def labelSetPartial (B : CombinatorialClass) (n : ℕ) : PowerSeries ℚ :=
  ∑ k ∈ Finset.range (n + 1), ((k.factorial : ℚ)⁻¹) • ((B.egf : PowerSeries ℚ) ^ k)

lemma coeff_labelSetPartial (B : CombinatorialClass) (n m : ℕ) :
    coeff m (labelSetPartial B n) =
      ∑ k ∈ Finset.range (n + 1), coeff m ((B.egf : PowerSeries ℚ) ^ k) / k.factorial := by
  simp [labelSetPartial, div_eq_mul_inv, mul_comm]

lemma labelSetSeries_coeff_eq_partial (B : CombinatorialClass) (n : ℕ) :
    coeff n (labelSetSeries B) = coeff n (labelSetPartial B n) := by
  rw [labelSetSeries, coeff_mk, coeff_labelSetPartial]
  exact CombinatorialClass.labelSetCount_div_factorial_eq_partial_exp_coeff B n

lemma coeff_pow_eq_zero_of_constantCoeff_eq_zero {f : PowerSeries ℚ}
    (h0 : f.constantCoeff = 0) {n k : ℕ} (hnk : n < k) : coeff n (f ^ k) = 0 := by
  exact PowerSeries.coeff_of_lt_order n
    (lt_of_lt_of_le (by exact_mod_cast hnk)
      (PowerSeries.le_order_pow_of_constantCoeff_eq_zero k h0))

lemma posIntClass_egf_constantCoeff_zero :
    (posIntClass.egf : PowerSeries ℚ).constantCoeff = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_egf, posIntClass.count_zero]
  simp

lemma labelSetSeries_coeff_eq_partial_of_le (n m : ℕ) (hmn : m ≤ n) :
    coeff m (labelSetSeries posIntClass) = coeff m (labelSetPartial posIntClass n) := by
  rw [labelSetSeries_coeff_eq_partial posIntClass m, coeff_labelSetPartial, coeff_labelSetPartial]
  refine Finset.sum_subset
    (by
      intro k hk
      exact Finset.mem_range.mpr
        (Nat.lt_succ_of_le (le_trans (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) hmn)))
    ?_
  intro k hk hnkm
  rw [coeff_pow_eq_zero_of_constantCoeff_eq_zero posIntClass_egf_constantCoeff_zero]
  · simp
  · have hk' : ¬ k < m + 1 := by
      intro h
      exact hnkm (Finset.mem_range.mpr h)
    omega

lemma posIntClass_egf_derivative :
    d⁄dX ℚ posIntClass.egf = PowerSeries.exp ℚ := by
  ext n
  rw [coeff_derivative, coeff_exp, coeff_egf]
  rw [posIntClass.count_pos (by omega)]
  rw [Nat.factorial_succ]
  norm_num
  field_simp [Nat.cast_ne_zero.mpr n.factorial_pos.ne']

lemma deriv_labelSetPartial_term_succ (k : ℕ) :
    d⁄dX ℚ (((((k + 1).factorial : ℚ)⁻¹) • (posIntClass.egf ^ (k + 1)))) =
      ((k.factorial : ℚ)⁻¹) • (posIntClass.egf ^ k * PowerSeries.exp ℚ) := by
  change PowerSeries.derivativeFun
      (((((k + 1).factorial : ℚ)⁻¹) • (posIntClass.egf ^ (k + 1)))) = _
  rw [PowerSeries.derivativeFun_smul]
  rw [show PowerSeries.derivativeFun (posIntClass.egf ^ (k + 1)) =
      d⁄dX ℚ (posIntClass.egf ^ (k + 1)) by rfl]
  rw [PowerSeries.derivative_pow, posIntClass_egf_derivative]
  rw [Nat.cast_add_one, Nat.factorial_succ]
  norm_num
  ext m
  have hcoeff :
      coeff m (((↑k + 1 : PowerSeries ℚ) * (posIntClass.egf ^ k * PowerSeries.exp ℚ))) =
        (↑k + 1 : ℚ) * coeff m (posIntClass.egf ^ k * PowerSeries.exp ℚ) := by
    rw [show (↑k + 1 : PowerSeries ℚ) = PowerSeries.C (↑k + 1 : ℚ) by
      ext t
      cases t <;> simp]
    rw [PowerSeries.coeff_C_mul]
  rw [show (((↑k + 1 : PowerSeries ℚ) * posIntClass.egf ^ k * PowerSeries.exp ℚ)) =
      ((↑k + 1 : PowerSeries ℚ) * (posIntClass.egf ^ k * PowerSeries.exp ℚ)) by ring]
  simp only [coeff_smul]
  rw [hcoeff]
  simp [smul_eq_mul]
  field_simp [Nat.cast_ne_zero.mpr k.factorial_pos.ne', show (↑k + 1 : ℚ) ≠ 0 by positivity]

lemma labelSetPartial_derivative_succ (n : ℕ) :
    d⁄dX ℚ (labelSetPartial posIntClass (n + 1)) =
      PowerSeries.exp ℚ * labelSetPartial posIntClass n := by
  rw [labelSetPartial]
  rw [map_sum]
  rw [Finset.sum_range_succ']
  simp only [pow_zero]
  rw [show (d⁄dX ℚ) ((((0 : ℕ).factorial : ℚ)⁻¹) • (1 : PowerSeries ℚ)) = 0 by simp]
  rw [add_zero]
  simp_rw [deriv_labelSetPartial_term_succ]
  rw [labelSetPartial]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [show PowerSeries.exp ℚ * (((k.factorial : ℚ)⁻¹) • (posIntClass.egf ^ k)) =
      ((k.factorial : ℚ)⁻¹) • (posIntClass.egf ^ k * PowerSeries.exp ℚ) by
    simp
    ring_nf]

lemma labelSetSeries_derivative :
    d⁄dX ℚ (labelSetSeries posIntClass) =
      PowerSeries.exp ℚ * labelSetSeries posIntClass := by
  ext n
  rw [coeff_derivative]
  rw [show coeff (n + 1) (labelSetSeries posIntClass) =
      coeff (n + 1) (labelSetPartial posIntClass (n + 1)) by
    exact labelSetSeries_coeff_eq_partial posIntClass (n + 1)]
  rw [← coeff_derivative]
  rw [labelSetPartial_derivative_succ]
  rw [coeff_mul, coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have hp2 : p.2 ≤ n := by
    have := Finset.mem_antidiagonal.mp hp
    omega
  rw [← labelSetSeries_coeff_eq_partial_of_le n p.2 hp2]

lemma bellSeries_derivative :
    d⁄dX ℚ bellSeries = PowerSeries.exp ℚ * bellSeries := by
  ext n
  rw [coeff_derivative, coeff_mul, bellSeries, PowerSeries.coeff_mk, Nat.bell_succ']
  simp only [PowerSeries.coeff_exp, PowerSeries.coeff_mk]
  rw [Nat.factorial_succ, Nat.cast_mul]
  have hleft :
      (↑(∑ ij ∈ antidiagonal n, n.choose ij.1 * ij.2.bell) /
          ((n + 1 : ℕ) : ℚ) / ↑n.factorial * (↑n + 1) : ℚ) =
        (↑(∑ ij ∈ antidiagonal n, n.choose ij.1 * ij.2.bell) / ↑n.factorial : ℚ) := by
    rw [show (((n + 1 : ℕ) : ℚ)) = (n : ℚ) + 1 by norm_num]
    field_simp [Nat.cast_ne_zero.mpr n.factorial_pos.ne', show ((n : ℚ) + 1) ≠ 0 by positivity]
  rw [div_mul_eq_div_div, hleft, Nat.cast_sum, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  have hk_le : ij.1 ≤ n := by
    have hsum : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
    omega
  have hfac :
      ((n.choose ij.1 : ℚ) * Nat.bell ij.2) * (↑n.factorial)⁻¹ =
        (1 / (ij.1.factorial : ℚ)) * ((Nat.bell ij.2 : ℚ) / ij.2.factorial) := by
    have hchoose := Nat.choose_mul_factorial_mul_factorial hk_le
    have hsum : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
    have hsub : n - ij.1 = ij.2 := by omega
    rw [hsub] at hchoose
    have hchooseQ : (n.choose ij.1 : ℚ) * ij.1.factorial * ij.2.factorial = n.factorial := by
      exact_mod_cast hchoose
    field_simp [Nat.cast_ne_zero.mpr n.factorial_pos.ne',
      Nat.cast_ne_zero.mpr ij.1.factorial_pos.ne',
      Nat.cast_ne_zero.mpr ij.2.factorial_pos.ne']
    linear_combination (Nat.bell ij.2 : ℚ) * hchooseQ
  norm_num [Nat.cast_mul]
  rw [hfac]
  simp

lemma labelSetSeries_eq_bellSeries :
    labelSetSeries posIntClass = bellSeries := by
  ext n
  refine Nat.strong_induction_on n ?_
  intro n ih
  cases n with
  | zero =>
      rw [labelSetSeries_coeff_eq_partial posIntClass 0, bellSeries, PowerSeries.coeff_mk]
      simp [labelSetPartial, Nat.bell_zero]
  | succ n =>
      have hS := congrArg (coeff n) labelSetSeries_derivative
      have hB := congrArg (coeff n) bellSeries_derivative
      rw [coeff_derivative, coeff_mul] at hS
      rw [coeff_derivative, coeff_mul] at hB
      have hrhs :
          (∑ p ∈ antidiagonal n, coeff p.1 (PowerSeries.exp ℚ) *
            coeff p.2 (labelSetSeries posIntClass)) =
          (∑ p ∈ antidiagonal n, coeff p.1 (PowerSeries.exp ℚ) * coeff p.2 bellSeries) := by
        apply Finset.sum_congr rfl
        intro p hp
        have hp2 : p.2 < n + 1 := by
          have := Finset.mem_antidiagonal.mp hp
          omega
        rw [ih p.2 hp2]
      have hmul : coeff (n + 1) (labelSetSeries posIntClass) * (n + 1) =
          coeff (n + 1) bellSeries * (n + 1) := by
        rw [hS, hB, hrhs]
      exact mul_right_cancel₀ (show (↑n + 1 : ℚ) ≠ 0 by positivity) hmul

theorem labelSetCount_posIntClass_eq_bell (n : ℕ) :
    labelSetCount posIntClass n = (Nat.bell n : ℚ) := by
  have h := congrArg (coeff n) labelSetSeries_eq_bellSeries
  simp [labelSetSeries, bellSeries] at h
  field_simp [Nat.cast_ne_zero.mpr n.factorial_pos.ne'] at h
  exact h
