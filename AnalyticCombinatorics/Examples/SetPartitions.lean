import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass
import AnalyticCombinatorics.PartA.Ch2.LabelledClass
import AnalyticCombinatorics.Examples.Compositions
import Mathlib.Combinatorics.Enumerative.Bell
import Mathlib.Combinatorics.Enumerative.Stirling

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

/-! Sanity checks: Bell sequence starts 1, 1, 2, 5, 15, 52, 203, ... -/

example : labelSetCount posIntClass 0 = (1 : ℚ) := by
  rw [labelSetCount_posIntClass_eq_bell]
  norm_num

example : labelSetCount posIntClass 1 = (1 : ℚ) := by
  rw [labelSetCount_posIntClass_eq_bell]
  norm_num

example : labelSetCount posIntClass 2 = (2 : ℚ) := by
  rw [labelSetCount_posIntClass_eq_bell]
  norm_num

example : labelSetCount posIntClass 3 = (5 : ℚ) := by
  rw [labelSetCount_posIntClass_eq_bell]
  rw [show 3 = 2 + 1 by rfl, Nat.bell_succ']
  norm_num [Finset.antidiagonal]

example : labelSetCount posIntClass 4 = (15 : ℚ) := by
  rw [labelSetCount_posIntClass_eq_bell]
  have h3 : Nat.bell 3 = 5 := by
    rw [show 3 = 2 + 1 by rfl, Nat.bell_succ']
    norm_num [Finset.antidiagonal]
  rw [show 4 = 3 + 1 by rfl, Nat.bell_succ']
  norm_num [Finset.antidiagonal, h3]

private lemma bell_three_sanity : Nat.bell 3 = 5 := by
  rw [show 3 = 2 + 1 by rfl, Nat.bell_succ']
  norm_num [Finset.antidiagonal]

private lemma bell_four_sanity : Nat.bell 4 = 15 := by
  rw [show 4 = 3 + 1 by rfl, Nat.bell_succ']
  norm_num [Finset.antidiagonal, Nat.choose, bell_three_sanity]

private lemma bell_five_sanity : Nat.bell 5 = 52 := by
  rw [show 5 = 4 + 1 by rfl, Nat.bell_succ']
  norm_num [Finset.antidiagonal, Nat.choose, bell_three_sanity, bell_four_sanity]

private lemma bell_six_sanity : Nat.bell 6 = 203 := by
  rw [show 6 = 5 + 1 by rfl, Nat.bell_succ']
  norm_num [Finset.antidiagonal, Nat.choose, bell_three_sanity, bell_four_sanity,
    bell_five_sanity]

private lemma bell_seven_sanity : Nat.bell 7 = 877 := by
  rw [show 7 = 6 + 1 by rfl, Nat.bell_succ']
  norm_num [Finset.antidiagonal, Nat.choose, bell_three_sanity, bell_four_sanity,
    bell_five_sanity, bell_six_sanity]

example : labelSetCount posIntClass 5 = (52 : ℚ) := by
  rw [labelSetCount_posIntClass_eq_bell]
  norm_num [bell_five_sanity]

example : labelSetCount posIntClass 6 = (203 : ℚ) := by
  rw [labelSetCount_posIntClass_eq_bell]
  norm_num [bell_six_sanity]

example : labelSetCount posIntClass 7 = (877 : ℚ) := by
  rw [labelSetCount_posIntClass_eq_bell]
  norm_num [bell_seven_sanity]

/-!
Mathlib names the Stirling numbers of the second kind `Nat.stirlingSecond`;
this is the local naming bridge for the requested `stirling2` convention.
-/

lemma posIntClass_egf_add_one_eq_exp :
    posIntClass.egf + 1 = PowerSeries.exp ℚ := by
  ext n
  cases n with
  | zero =>
      rw [map_add, coeff_egf, posIntClass.count_zero, PowerSeries.coeff_one,
        PowerSeries.coeff_exp]
      norm_num
  | succ n =>
      rw [map_add, coeff_egf, posIntClass.count_pos (Nat.succ_pos n), PowerSeries.coeff_one,
        PowerSeries.coeff_exp]
      simp

lemma derivative_posIntClass_egf_pow_succ (k : ℕ) :
    d⁄dX ℚ (posIntClass.egf ^ (k + 1)) =
      ((k + 1 : ℕ) : PowerSeries ℚ) *
        (posIntClass.egf ^ (k + 1) + posIntClass.egf ^ k) := by
  rw [PowerSeries.derivative_pow, posIntClass_egf_derivative, ← posIntClass_egf_add_one_eq_exp]
  simp [pow_succ]
  ring

lemma coeff_derivative_posIntClass_egf_pow_succ (n k : ℕ) :
    coeff n (d⁄dX ℚ (posIntClass.egf ^ (k + 1))) =
      (k + 1 : ℚ) *
        (coeff n (posIntClass.egf ^ (k + 1)) + coeff n (posIntClass.egf ^ k)) := by
  rw [derivative_posIntClass_egf_pow_succ]
  rw [show ((k + 1 : ℕ) : PowerSeries ℚ) = PowerSeries.C ((k + 1 : ℕ) : ℚ) by
    ext t
    cases t <;> simp]
  rw [PowerSeries.coeff_C_mul, map_add]
  norm_num

lemma coeff_posIntClass_egf_pow_eq_factorial_mul_stirlingSecond (n k : ℕ) :
    coeff n (posIntClass.egf ^ k) =
      (((k.factorial * Nat.stirlingSecond n k : ℕ) : ℚ) / n.factorial) := by
  revert k
  induction n with
  | zero =>
      intro k
      cases k with
      | zero =>
          simp [Nat.stirlingSecond_zero]
      | succ k =>
          rw [coeff_pow_eq_zero_of_constantCoeff_eq_zero posIntClass_egf_constantCoeff_zero
            (show 0 < k + 1 by omega)]
          simp [Nat.stirlingSecond_zero_succ]
  | succ n ih =>
      intro k
      cases k with
      | zero =>
          simp [Nat.stirlingSecond_succ_zero]
      | succ k =>
          have hderiv := coeff_derivative_posIntClass_egf_pow_succ n k
          rw [coeff_derivative] at hderiv
          rw [ih (k + 1), ih k] at hderiv
          apply mul_right_cancel₀ (show (n : ℚ) + 1 ≠ 0 by positivity)
          calc
            coeff (n + 1) (posIntClass.egf ^ (k + 1)) * ((n : ℚ) + 1)
                = (k + 1 : ℚ) *
                    (((((k + 1).factorial * Nat.stirlingSecond n (k + 1) : ℕ) : ℚ) /
                        n.factorial) +
                      ((((k.factorial * Nat.stirlingSecond n k : ℕ) : ℚ) / n.factorial))) :=
                  hderiv
            _ = (((((k + 1).factorial * Nat.stirlingSecond (n + 1) (k + 1) : ℕ) : ℚ) /
                    (n + 1).factorial) * ((n : ℚ) + 1)) := by
                  rw [Nat.stirlingSecond_succ_succ]
                  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_add_one]
                  field_simp [Nat.cast_ne_zero.mpr n.factorial_pos.ne',
                    show (n : ℚ) + 1 ≠ 0 by positivity]

/-- Stirling 2nd kind connection: ordered set partitions of `{1, ..., n}` into `k` blocks.

Mathlib's identifier for the Stirling number of the second kind is `Nat.stirlingSecond`.
-/
theorem labelPow_posIntClass_count_eq_factorial_mul_stirlingSecond (n k : ℕ) :
    (CombinatorialClass.labelPow posIntClass k).count n =
      k.factorial * Nat.stirlingSecond n k := by
  have hpow := CombinatorialClass.labelPow_count_div_factorial_eq_coeff_pow posIntClass k n
  rw [coeff_posIntClass_egf_pow_eq_factorial_mul_stirlingSecond] at hpow
  field_simp [Nat.cast_ne_zero.mpr n.factorial_pos.ne'] at hpow
  exact_mod_cast hpow

/-- The labelled SEQ of `posIntClass` at size `n` counts ordered set partitions
    of `{1, ..., n}` (Fubini / ordered Bell number). The closed form is the sum
    `∑ k ∈ Finset.range (n + 1), k! * S(n, k)`. -/
theorem labelSeq_posIntClass_count_eq_fubini (n : ℕ) :
    (labelSeq posIntClass posIntClass.count_zero).count n =
      ∑ k ∈ Finset.range (n + 1), k.factorial * Nat.stirlingSecond n k := by
  rw [labelSeq.count_eq]
  apply Finset.sum_congr rfl
  intro k _
  exact labelPow_posIntClass_count_eq_factorial_mul_stirlingSecond n k

/-! Sanity: Fubini numbers are 1, 1, 3, 13, 75, 541, 4683.
    a(0) = ∑ k ∈ range 1, k! · S(0,k) = 1.
    a(1) = ∑ k ∈ range 2, k! · S(1,k) = 1.
    a(2) = ∑ k ∈ range 3, k! · S(2,k) = 0!·0 + 1!·1 + 2!·1 = 3.
    a(3) = 0!·0 + 1!·1 + 2!·3 + 3!·1 = 1 + 6 + 6 = 13. -/
example : (labelSeq posIntClass posIntClass.count_zero).count 0 = 1 := by
  rw [labelSeq_posIntClass_count_eq_fubini]
  decide

example : (labelSeq posIntClass posIntClass.count_zero).count 1 = 1 := by
  rw [labelSeq_posIntClass_count_eq_fubini]
  decide

example : (labelSeq posIntClass posIntClass.count_zero).count 2 = 3 := by
  rw [labelSeq_posIntClass_count_eq_fubini]
  decide

example : (labelSeq posIntClass posIntClass.count_zero).count 3 = 13 := by
  rw [labelSeq_posIntClass_count_eq_fubini]
  decide

example : (labelSeq posIntClass posIntClass.count_zero).count 4 = 75 := by
  rw [labelSeq_posIntClass_count_eq_fubini]
  decide

example : (labelSeq posIntClass posIntClass.count_zero).count 5 = 541 := by
  rw [labelSeq_posIntClass_count_eq_fubini]
  decide

example : (labelSeq posIntClass posIntClass.count_zero).count 6 = 4683 := by
  rw [labelSeq_posIntClass_count_eq_fubini]
  decide

/-! Sanity: ordered set partitions count = k! · S(n,k).
    S(2,1) = 1, S(2,2) = 1.
    S(3,1) = 1, S(3,2) = 3, S(3,3) = 1.
    S(4,2) = 7, S(4,3) = 6. -/

example : (CombinatorialClass.labelPow posIntClass 1).count 2 = 1 := by
  rw [labelPow_posIntClass_count_eq_factorial_mul_stirlingSecond]
  decide

example : (CombinatorialClass.labelPow posIntClass 2).count 3 = 6 := by
  rw [labelPow_posIntClass_count_eq_factorial_mul_stirlingSecond]
  decide

example : (CombinatorialClass.labelPow posIntClass 3).count 4 = 36 := by
  rw [labelPow_posIntClass_count_eq_factorial_mul_stirlingSecond]
  decide

example : (CombinatorialClass.labelPow posIntClass 2).count 4 = 14 := by
  rw [labelPow_posIntClass_count_eq_factorial_mul_stirlingSecond]
  decide  -- 2! · S(4,2) = 2 · 7 = 14

example : (CombinatorialClass.labelPow posIntClass 3).count 5 = 150 := by
  rw [labelPow_posIntClass_count_eq_factorial_mul_stirlingSecond]
  decide  -- 3! · S(5,3) = 6 · 25 = 150

example : (CombinatorialClass.labelPow posIntClass 2).count 5 = 30 := by
  rw [labelPow_posIntClass_count_eq_factorial_mul_stirlingSecond]
  decide  -- 2! · S(5,2) = 2 · 15 = 30

/-! Sanity: labelled cycles of nonempty sets are cyclically ordered set partitions.
    The values are `0, 1, 2, 6, 26, 150, 1082, ...`; for positive `n` this is
    OEIS A000629 with index shifted by one. -/

theorem labelCycCount_posIntClass_eq_cyclic_fubini (n : ℕ) :
    labelCycCount posIntClass n =
      ∑ k ∈ Finset.range (n + 1), if k = 0 then 0 else
        (((k - 1).factorial * Nat.stirlingSecond n k : ℕ) : ℚ) := by
  rw [CombinatorialClass.labelCycCount]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k = 0
  · simp [hk]
  · simp only [if_neg hk]
    rw [labelPow_posIntClass_count_eq_factorial_mul_stirlingSecond]
    cases k with
    | zero => contradiction
    | succ k =>
        rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_mul]
        simp only [add_tsub_cancel_right]
        field_simp [show (k : ℚ) + 1 ≠ 0 by positivity]
        rw [Nat.cast_mul]

example : labelCycCount posIntClass 0 = 0 := by
  rw [labelCycCount_posIntClass_eq_cyclic_fubini]
  norm_num [Finset.sum_range_succ, Nat.factorial, Nat.stirlingSecond]

example : labelCycCount posIntClass 1 = 1 := by
  rw [labelCycCount_posIntClass_eq_cyclic_fubini]
  norm_num [Finset.sum_range_succ, Nat.factorial, Nat.stirlingSecond]

example : labelCycCount posIntClass 2 = 2 := by
  rw [labelCycCount_posIntClass_eq_cyclic_fubini]
  norm_num [Finset.sum_range_succ, Nat.factorial, Nat.stirlingSecond]

example : labelCycCount posIntClass 3 = 6 := by
  rw [labelCycCount_posIntClass_eq_cyclic_fubini]
  norm_num [Finset.sum_range_succ, Nat.factorial, Nat.stirlingSecond]

example : labelCycCount posIntClass 4 = 26 := by
  rw [labelCycCount_posIntClass_eq_cyclic_fubini]
  norm_num [Finset.sum_range_succ, Nat.factorial, Nat.factorial_succ, Nat.stirlingSecond]

example : labelCycCount posIntClass 5 = 150 := by
  rw [labelCycCount_posIntClass_eq_cyclic_fubini]
  norm_num [Finset.sum_range_succ, Nat.factorial, Nat.factorial_succ, Nat.stirlingSecond]

example : labelCycCount posIntClass 6 = 1082 := by
  rw [labelCycCount_posIntClass_eq_cyclic_fubini]
  norm_num [Finset.sum_range_succ, Nat.factorial, Nat.factorial_succ, Nat.stirlingSecond]

/-- `posIntClass.egf = exp(z) - 1`. -/
theorem posIntClass_egf_eq_exp_sub_one :
    posIntClass.egf = PowerSeries.exp ℚ - 1 := by
  rw [← posIntClass_egf_add_one_eq_exp]
  ring

/-- The Fubini EGF satisfies `(2 - exp(z)) · F = 1`. -/
theorem labelSeq_posIntClass_egf_mul_two_sub_exp :
    (CombinatorialClass.labelSeq posIntClass posIntClass.count_zero).egf
      * (2 - PowerSeries.exp ℚ) = 1 := by
  have h := CombinatorialClass.labelSeq_egf_mul_one_sub_egf posIntClass posIntClass.count_zero
  rw [posIntClass_egf_eq_exp_sub_one] at h
  rw [show (1 - (PowerSeries.exp ℚ - 1) : PowerSeries ℚ) =
      2 - PowerSeries.exp ℚ by ring] at h
  rw [mul_comm]
  exact h

/-! Sanity: labelled product of permutations and nonempty sets.
    Its EGF is `permClass.egf * posIntClass.egf = (1 / (1 - X)) * (exp X - 1)`. -/

theorem labelProdCount_permClass_posIntClass_eq_sum (n : ℕ) :
    CombinatorialClass.labelProdCount permClass posIntClass n =
      ∑ k ∈ Finset.range n, n.choose k * k.factorial := by
  rw [CombinatorialClass.labelProdCount]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [Finset.sum_range_succ]
  simp only [permClass_count_eq_factorial, Nat.sub_self, posIntClass.count_zero,
    mul_zero, Nat.choose_self, add_zero]
  apply Finset.sum_congr rfl
  intro k hk
  have hklt : k < n := Finset.mem_range.mp hk
  rw [posIntClass.count_pos (by omega)]
  simp

theorem labelProdCount_permClass_posIntClass_div_factorial_eq_coeff_exp_sub_one (n : ℕ) :
    (CombinatorialClass.labelProdCount permClass posIntClass n : ℚ) / n.factorial =
      coeff n (permClass.egf * (PowerSeries.exp ℚ - 1)) := by
  rw [CombinatorialClass.labelProdCount_div_factorial_eq_coeff_mul_egf,
    posIntClass_egf_eq_exp_sub_one]

example : CombinatorialClass.labelProdCount permClass posIntClass 0 = 0 := by
  rw [labelProdCount_permClass_posIntClass_eq_sum]
  simp

example : CombinatorialClass.labelProdCount permClass posIntClass 1 = 1 := by
  rw [labelProdCount_permClass_posIntClass_eq_sum]
  norm_num [Nat.factorial]

example : CombinatorialClass.labelProdCount permClass posIntClass 2 = 3 := by
  rw [labelProdCount_permClass_posIntClass_eq_sum]
  decide

/-! Bell EGF identities, parallel to the Fubini EGF identity above. -/

/-- The Bell EGF has coefficient `Bell n / n!`. -/
theorem coeff_bellSeries_eq_bell_div_factorial (n : ℕ) :
    coeff n bellSeries = (Nat.bell n : ℚ) / n.factorial := by
  rw [bellSeries, PowerSeries.coeff_mk]

/-- Sanity: the labelled SET EGF over nonempty sets has coefficient `Bell n / n!`. -/
theorem coeff_labelSetSeries_posIntClass_eq_bell_div_factorial (n : ℕ) :
    coeff n (labelSetSeries posIntClass) = (Nat.bell n : ℚ) / n.factorial := by
  rw [labelSetSeries_eq_bellSeries, coeff_bellSeries_eq_bell_div_factorial]

/-- The Bell EGF as a labelled SET construction is `bellSeries`. -/
theorem labelSetSeries_posIntClass_eq_bellSeries :
    labelSetSeries posIntClass = bellSeries :=
  labelSetSeries_eq_bellSeries

/-- Bell EGF identity. Mathlib's power-series composition API is `subst`. -/
theorem bellSeries_eq_exp_subst_posIntClass_egf :
    bellSeries = (PowerSeries.exp ℚ).subst posIntClass.egf := by
  rw [← labelSetSeries_eq_bellSeries]
  ext n
  rw [labelSetSeries_coeff_eq_partial posIntClass n, coeff_labelSetPartial]
  rw [PowerSeries.coeff_subst'
    (PowerSeries.HasSubst.of_constantCoeff_zero' posIntClass_egf_constantCoeff_zero)]
  rw [finsum_eq_sum_of_support_subset]
  · apply Finset.sum_congr rfl
    intro k _
    rw [PowerSeries.coeff_exp]
    simp [div_eq_mul_inv, smul_eq_mul, mul_comm]
  · rw [Function.support_subset_iff']
    intro k hk
    have hnk : n < k := by
      have hk' : ¬ k < n + 1 := by simpa using hk
      omega
    rw [coeff_pow_eq_zero_of_constantCoeff_eq_zero posIntClass_egf_constantCoeff_zero hnk]
    simp

/-- Bell ODE in `posIntClass.egf = exp(z) - 1` form:
    `B' = (1 + posIntClass.egf) * B`. -/
theorem labelSetSeries_posIntClass_derivative_eq_one_add_egf_mul :
    d⁄dX ℚ (labelSetSeries posIntClass) =
      (1 + posIntClass.egf) * labelSetSeries posIntClass := by
  rw [labelSetSeries_derivative, ← posIntClass_egf_add_one_eq_exp]
  ring

/-- The same Bell ODE for the named Bell-number EGF. -/
theorem bellSeries_derivative_eq_one_add_posIntClass_egf_mul :
    d⁄dX ℚ bellSeries = (1 + posIntClass.egf) * bellSeries := by
  rw [bellSeries_derivative, ← posIntClass_egf_add_one_eq_exp]
  ring

example (n : ℕ) :
    labelSetCount posIntClass n / (n.factorial : ℚ) =
      (Nat.bell n : ℚ) / n.factorial := by
  rw [labelSetCount_posIntClass_eq_bell]

example (n : ℕ) :
    (CombinatorialClass.labelSeq posIntClass posIntClass.count_zero).count n =
      ∑ k ∈ Finset.range (n + 1), k.factorial * Nat.stirlingSecond n k :=
  labelSeq_posIntClass_count_eq_fubini n

private lemma bell_eight_sanity : Nat.bell 8 = 4140 := by
  rw [show 8 = 7 + 1 by rfl, Nat.bell_succ']
  norm_num [Finset.antidiagonal, Nat.choose, bell_three_sanity, bell_four_sanity,
    bell_five_sanity, bell_six_sanity, bell_seven_sanity]

private lemma bell_nine_sanity : Nat.bell 9 = 21147 := by
  rw [show 9 = 8 + 1 by rfl, Nat.bell_succ']
  norm_num [Finset.antidiagonal, Nat.choose, bell_three_sanity, bell_four_sanity,
    bell_five_sanity, bell_six_sanity, bell_seven_sanity, bell_eight_sanity]

private lemma bell_ten_sanity : Nat.bell 10 = 115975 := by
  rw [show 10 = 9 + 1 by rfl, Nat.bell_succ']
  norm_num [Finset.antidiagonal, Nat.choose, bell_three_sanity, bell_four_sanity,
    bell_five_sanity, bell_six_sanity, bell_seven_sanity, bell_eight_sanity,
    bell_nine_sanity]

example : labelSetCount posIntClass 8 = (4140 : ℚ) := by
  rw [labelSetCount_posIntClass_eq_bell]
  norm_num [bell_eight_sanity]

example : labelSetCount posIntClass 9 = (21147 : ℚ) := by
  rw [labelSetCount_posIntClass_eq_bell]
  norm_num [bell_nine_sanity]

example : labelSetCount posIntClass 10 = (115975 : ℚ) := by
  rw [labelSetCount_posIntClass_eq_bell]
  norm_num [bell_ten_sanity]

example : (CombinatorialClass.labelSeq posIntClass posIntClass.count_zero).count 7 = 47293 := by
  rw [labelSeq_posIntClass_count_eq_fubini]
  decide

example : (CombinatorialClass.labelSeq posIntClass posIntClass.count_zero).count 8 = 545835 := by
  rw [labelSeq_posIntClass_count_eq_fubini]
  decide

/-!
## Narayana blocker

This Mathlib snapshot provides `catalan`, `Nat.stirlingFirst`, and `Nat.stirlingSecond`, but
source search and Lean `#check` found no `Nat.narayana` or root-level `narayana` identifier.
Thus the usual Narayana formula
`N(n,k) = (1 / n) * (n.choose k) * (n.choose (k - 1))` and the Catalan summation
`∑ k = 1..n, N(n,k) = catalan n` do not currently have a Mathlib Narayana-number target to
connect to here.

The available labelled-cycle bridge to the unsigned Stirling numbers of the first kind is recorded
below: one labelled cycle on atoms is a permutation with exactly one cycle.
-/

/-- Labelled cycles on atoms count permutations with one cycle, i.e. the unsigned Stirling
number of the first kind `Nat.stirlingFirst n 1`. -/
theorem labelCycCount_Atom_eq_stirlingFirst_one (n : ℕ) :
    labelCycCount Atom n = (Nat.stirlingFirst n 1 : ℚ) := by
  cases n with
  | zero =>
      simp [CombinatorialClass.labelCycCount, Nat.stirlingFirst_zero_succ]
  | succ n =>
      rw [labelCycCount_Atom_succ, Nat.stirlingFirst_one_right]

private lemma stirlingFirst_shifted_sum_eq_sum (n : ℕ) (hn : n ≠ 0) :
    (∑ k ∈ Finset.range (n + 1), Nat.stirlingFirst n (k + 1)) =
      ∑ k ∈ Finset.range (n + 1), Nat.stirlingFirst n k := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ']
  have hzero : Nat.stirlingFirst n 0 = 0 := by
    cases n with
    | zero => contradiction
    | succ n => simp
  have htop : Nat.stirlingFirst n (n + 1) = 0 :=
    Nat.stirlingFirst_eq_zero_of_lt (Nat.lt_succ_self n)
  simp [hzero, htop]

/-- Summing the unsigned Stirling numbers of the first kind over the number of cycles gives
the total number of permutations of `n` labelled elements. -/
theorem stirlingFirst_sum_eq_factorial (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), Nat.stirlingFirst n k = n.factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ']
      simp only [Nat.stirlingFirst_succ_zero, add_zero]
      simp_rw [Nat.stirlingFirst_succ_succ]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      by_cases hn : n = 0
      · subst n
        simp
      · rw [stirlingFirst_shifted_sum_eq_sum n hn, ih]
        simp [Nat.factorial_succ, Nat.succ_mul]

example (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), Nat.stirlingFirst n k = n.factorial := by
  exact stirlingFirst_sum_eq_factorial n

/-- Summing Stirling numbers of the second kind over the number of blocks gives
the Bell number. -/
theorem stirlingSecond_sum_eq_bell (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), Nat.stirlingSecond n k = Nat.bell n := by
  have h := labelSetCount_posIntClass_eq_bell n
  rw [CombinatorialClass.labelSetCount] at h
  have hsum :
      (∑ k ∈ Finset.range (n + 1),
          ((CombinatorialClass.labelPow posIntClass k).count n : ℚ) / k.factorial) =
        ∑ k ∈ Finset.range (n + 1), (Nat.stirlingSecond n k : ℚ) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [labelPow_posIntClass_count_eq_factorial_mul_stirlingSecond]
    rw [Nat.cast_mul]
    field_simp [Nat.cast_ne_zero.mpr k.factorial_pos.ne']
  rw [hsum] at h
  have hcast :
      ((∑ k ∈ Finset.range (n + 1), Nat.stirlingSecond n k : ℕ) : ℚ) =
        (Nat.bell n : ℚ) := by
    rw [Nat.cast_sum]
    exact h
  exact_mod_cast hcast

example (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), Nat.stirlingSecond n k = Nat.bell n := by
  exact stirlingSecond_sum_eq_bell n

private lemma bell_eleven_sanity : Nat.bell 11 = 678570 := by
  rw [show 11 = 10 + 1 by rfl, Nat.bell_succ']
  norm_num [Finset.antidiagonal, Nat.choose, bell_three_sanity, bell_four_sanity,
    bell_five_sanity, bell_six_sanity, bell_seven_sanity, bell_eight_sanity,
    bell_nine_sanity, bell_ten_sanity]

/-! Bell sequence sanity dump: 1,1,2,5,15,52,203,877,4140,21147,115975,678570. -/
example : labelSetCount posIntClass 11 = (678570 : ℚ) := by
  rw [labelSetCount_posIntClass_eq_bell]
  norm_num [bell_eleven_sanity]

set_option linter.style.nativeDecide false in
example : labelSetCount posIntClass 12 = (4213597 : ℚ) := by
  rw [labelSetCount_posIntClass_eq_bell]
  native_decide

set_option linter.style.nativeDecide false in
example : labelSetCount posIntClass 13 = (27644437 : ℚ) := by
  rw [labelSetCount_posIntClass_eq_bell]
  native_decide

set_option linter.style.nativeDecide false in
example : labelSetCount posIntClass 14 = (190899322 : ℚ) := by
  rw [labelSetCount_posIntClass_eq_bell]
  native_decide

set_option linter.style.nativeDecide false in
example : labelSetCount posIntClass 15 = (1382958545 : ℚ) := by
  rw [labelSetCount_posIntClass_eq_bell]
  native_decide

example (n : ℕ) :
    CombinatorialClass.labelCycCount posIntClass n =
      ∑ k ∈ Finset.range (n + 1),
        if k = 0 then 0
        else ((k - 1).factorial * Nat.stirlingSecond n k : ℚ) := by
  rw [labelCycCount_posIntClass_eq_cyclic_fubini]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k = 0
  · simp [hk]
  · simp [hk, Nat.cast_mul]

example : CombinatorialClass.labelCycCount posIntClass 5 = (150 : ℚ) := by
  rw [labelCycCount_posIntClass_eq_cyclic_fubini]
  norm_num [Finset.sum_range_succ, Nat.factorial, Nat.factorial_succ, Nat.stirlingSecond]

example : CombinatorialClass.labelCycCount posIntClass 6 = (1082 : ℚ) := by
  rw [labelCycCount_posIntClass_eq_cyclic_fubini]
  norm_num [Finset.sum_range_succ, Nat.factorial, Nat.factorial_succ, Nat.stirlingSecond]

example : CombinatorialClass.labelCycCount posIntClass 7 = (9366 : ℚ) := by
  rw [labelCycCount_posIntClass_eq_cyclic_fubini]
  norm_num [Finset.sum_range_succ, Nat.factorial, Nat.factorial_succ, Nat.stirlingSecond]

/-! Unsigned Stirling numbers of the first kind sanity dump. -/

example : Nat.stirlingFirst 0 0 = 1 := by
  rw [Nat.stirlingFirst_zero]

example (n : ℕ) : Nat.stirlingFirst (n + 1) 0 = 0 := by
  rw [Nat.stirlingFirst_succ_zero]

example (n : ℕ) : Nat.stirlingFirst n n = 1 := by
  rw [Nat.stirlingFirst_self]

example : Nat.stirlingFirst 3 1 = 2 := by
  decide

example : Nat.stirlingFirst 4 2 = 11 := by
  decide

example : Nat.stirlingFirst 5 3 = 35 := by
  decide

example : ∑ k ∈ Finset.range 4, Nat.stirlingFirst 3 k = 6 := by
  rw [stirlingFirst_sum_eq_factorial]
  decide

example : ∑ k ∈ Finset.range 5, Nat.stirlingFirst 4 k = 24 := by
  rw [stirlingFirst_sum_eq_factorial]
  decide

example : ∑ k ∈ Finset.range 6, Nat.stirlingFirst 5 k = 120 := by
  rw [stirlingFirst_sum_eq_factorial]
  decide

example : ∑ k ∈ Finset.range 4, Nat.stirlingSecond 3 k = Nat.bell 3 := by
  rw [stirlingSecond_sum_eq_bell]

example : ∑ k ∈ Finset.range 5, Nat.stirlingSecond 4 k = Nat.bell 4 := by
  rw [stirlingSecond_sum_eq_bell]

example : ∑ k ∈ Finset.range 6, Nat.stirlingSecond 5 k = Nat.bell 5 := by
  rw [stirlingSecond_sum_eq_bell]

example : Nat.stirlingSecond 4 2 = 7 := by decide
example : Nat.stirlingSecond 5 3 = 25 := by decide
example : Nat.stirlingFirst 4 2 = 11 := by decide
example : Nat.stirlingFirst 5 3 = 35 := by decide

/-- Bell recurrence in the project-facing `range` form.

Mathlib provides the recurrence as `Nat.bell_succ'`, indexed by
`Finset.antidiagonal`; this is the same identity after reflecting the finite
sum and using binomial symmetry. -/
theorem bell_recurrence (n : ℕ) :
    Nat.bell (n + 1) = ∑ k ∈ Finset.range (n + 1), Nat.choose n k * Nat.bell k := by
  rw [Nat.bell_succ']
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun x y => Nat.choose n x * Nat.bell y) n]
  rw [← Finset.sum_range_reflect (fun k => Nat.choose n k * Nat.bell (n - k)) (n + 1)]
  apply Finset.sum_congr rfl
  intro k hk
  have hk_le : k ≤ n := by
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  simp only [Nat.add_sub_cancel]
  rw [Nat.sub_sub_self hk_le]
  rw [Nat.choose_symm hk_le]

example : Nat.bell 1 = Nat.choose 0 0 * Nat.bell 0 := by
  rw [show 1 = 0 + 1 by rfl, bell_recurrence 0]
  norm_num [Finset.sum_range_succ, bell_three_sanity, bell_four_sanity]

example :
    Nat.bell 2 = Nat.choose 1 0 * Nat.bell 0 + Nat.choose 1 1 * Nat.bell 1 := by
  rw [show 2 = 1 + 1 by rfl, bell_recurrence 1]
  norm_num [Finset.sum_range_succ, bell_three_sanity, bell_four_sanity]

example :
    Nat.bell 3 =
      Nat.choose 2 0 * Nat.bell 0 + Nat.choose 2 1 * Nat.bell 1 +
        Nat.choose 2 2 * Nat.bell 2 := by
  rw [show 3 = 2 + 1 by rfl, bell_recurrence 2]
  norm_num [Finset.sum_range_succ, bell_three_sanity, bell_four_sanity]

example :
    Nat.bell 4 =
      Nat.choose 3 0 * Nat.bell 0 + Nat.choose 3 1 * Nat.bell 1 +
        Nat.choose 3 2 * Nat.bell 2 + Nat.choose 3 3 * Nat.bell 3 := by
  rw [show 4 = 3 + 1 by rfl, bell_recurrence 3]
  norm_num [Finset.sum_range_succ, bell_three_sanity, bell_four_sanity]

example :
    Nat.bell 5 =
      Nat.choose 4 0 * Nat.bell 0 + Nat.choose 4 1 * Nat.bell 1 +
        Nat.choose 4 2 * Nat.bell 2 + Nat.choose 4 3 * Nat.bell 3 +
          Nat.choose 4 4 * Nat.bell 4 := by
  rw [show 5 = 4 + 1 by rfl, bell_recurrence 4]
  norm_num [Finset.sum_range_succ, bell_three_sanity, bell_four_sanity]

/-- Project-facing name for the classical recurrence of Stirling numbers of the second kind. -/
theorem stirlingSecond_succ (n k : ℕ) :
    Nat.stirlingSecond (n + 1) (k + 1) =
      (k + 1) * Nat.stirlingSecond n (k + 1) + Nat.stirlingSecond n k := by
  exact Nat.stirlingSecond_succ_succ n k

/-- Project-facing name for the classical recurrence of unsigned Stirling numbers of the first
kind. -/
theorem stirlingFirst_succ (n k : ℕ) :
    Nat.stirlingFirst (n + 1) (k + 1) =
      n * Nat.stirlingFirst n (k + 1) + Nat.stirlingFirst n k := by
  exact Nat.stirlingFirst_succ_succ n k

/-! Complete `n = 6` Stirling sanity rows. -/

example : Nat.stirlingSecond 6 0 = 0 := by decide
example : Nat.stirlingSecond 6 1 = 1 := by decide
example : Nat.stirlingSecond 6 2 = 31 := by decide
example : Nat.stirlingSecond 6 3 = 90 := by decide
example : Nat.stirlingSecond 6 4 = 65 := by decide
example : Nat.stirlingSecond 6 5 = 15 := by decide
example : Nat.stirlingSecond 6 6 = 1 := by decide

example : ∑ k ∈ Finset.range 7, Nat.stirlingSecond 6 k = 203 := by decide

example : Nat.stirlingFirst 6 0 = 0 := by decide
example : Nat.stirlingFirst 6 1 = 120 := by decide
example : Nat.stirlingFirst 6 2 = 274 := by decide
example : Nat.stirlingFirst 6 3 = 225 := by decide
example : Nat.stirlingFirst 6 4 = 85 := by decide
example : Nat.stirlingFirst 6 5 = 15 := by decide
example : Nat.stirlingFirst 6 6 = 1 := by decide

example : ∑ k ∈ Finset.range 7, Nat.stirlingFirst 6 k = 720 := by decide

set_option linter.style.nativeDecide false in
example : labelSetCount posIntClass 16 = (10480142147 : ℚ) := by
  rw [labelSetCount_posIntClass_eq_bell]
  native_decide

set_option linter.style.nativeDecide false in
example : labelSetCount posIntClass 17 = (82864869804 : ℚ) := by
  rw [labelSetCount_posIntClass_eq_bell]
  native_decide

set_option linter.style.nativeDecide false in
example : labelSetCount posIntClass 18 = (682076806159 : ℚ) := by
  rw [labelSetCount_posIntClass_eq_bell]
  native_decide

set_option linter.style.nativeDecide false in
example : labelSetCount posIntClass 19 = (5832742205057 : ℚ) := by
  rw [labelSetCount_posIntClass_eq_bell]
  native_decide

set_option linter.style.nativeDecide false in
example : labelSetCount posIntClass 20 = (51724158235372 : ℚ) := by
  rw [labelSetCount_posIntClass_eq_bell]
  native_decide

example : Nat.stirlingSecond 2 1 = 1 := by
  rw [show 2 = 1 + 1 by rfl, show 1 = 0 + 1 by rfl, stirlingSecond_succ 1 0]
  decide

example : Nat.stirlingSecond 3 2 = 3 := by
  rw [show 3 = 2 + 1 by rfl, show 2 = 1 + 1 by rfl, stirlingSecond_succ 2 1]
  decide

example : Nat.stirlingSecond 4 2 = 7 := by
  rw [show 4 = 3 + 1 by rfl, show 2 = 1 + 1 by rfl, stirlingSecond_succ 3 1]
  decide

example : Nat.stirlingSecond 5 3 = 25 := by
  rw [show 5 = 4 + 1 by rfl, show 3 = 2 + 1 by rfl, stirlingSecond_succ 4 2]
  decide

example : Nat.stirlingFirst 2 1 = 1 := by
  rw [show 2 = 1 + 1 by rfl, show 1 = 0 + 1 by rfl, stirlingFirst_succ 1 0]
  decide

example : Nat.stirlingFirst 3 2 = 3 := by
  rw [show 3 = 2 + 1 by rfl, show 2 = 1 + 1 by rfl, stirlingFirst_succ 2 1]
  decide

example : Nat.stirlingFirst 4 2 = 11 := by
  rw [show 4 = 3 + 1 by rfl, show 2 = 1 + 1 by rfl, stirlingFirst_succ 3 1]
  decide

set_option linter.style.nativeDecide false in
example : labelSetCount posIntClass 21 = (474869816156751 : ℚ) := by
  rw [labelSetCount_posIntClass_eq_bell]
  native_decide

set_option linter.style.nativeDecide false in
example : labelSetCount posIntClass 22 = (4506715738447323 : ℚ) := by
  rw [labelSetCount_posIntClass_eq_bell]
  native_decide

set_option linter.style.nativeDecide false in
example : labelSetCount posIntClass 23 = (44152005855084346 : ℚ) := by
  rw [labelSetCount_posIntClass_eq_bell]
  native_decide

set_option linter.style.nativeDecide false in
example : labelSetCount posIntClass 24 = (445958869294805289 : ℚ) := by
  rw [labelSetCount_posIntClass_eq_bell]
  native_decide

set_option linter.style.nativeDecide false in
example : labelSetCount posIntClass 25 = (4638590332229999353 : ℚ) := by
  rw [labelSetCount_posIntClass_eq_bell]
  native_decide
