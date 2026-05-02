import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.FieldSimp
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass
import AnalyticCombinatorics.PartA.Ch2.LabelledClass

open Finset PowerSeries CombinatorialClass

set_option linter.style.nativeDecide false

/-- Inclusion-exclusion count of surjections from an `n`-set onto a `k`-set. -/
def surjCount (n k : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (k + 1), (-1) ^ j * (k.choose j : ℤ) * ((k - j : ℤ) ^ n)

theorem surjCount_zero_right (n : ℕ) :
    surjCount n 0 = if n = 0 then 1 else 0 := by
  cases n <;> simp [surjCount]

theorem surjCount_zero_left (k : ℕ) :
    surjCount 0 k = if k = 0 then 1 else 0 := by
  rw [surjCount]
  simp only [pow_zero, mul_one]
  exact Int.alternating_sum_range_choose

private lemma surjCount_cast_eq_reflected (n k : ℕ) :
    (surjCount n k : ℚ) =
      ∑ m ∈ Finset.range (k + 1),
        (-1 : ℚ) ^ (k - m) * (k.choose m : ℚ) * (m : ℚ) ^ n := by
  rw [surjCount]
  rw [show ((∑ j ∈ range (k + 1),
        (-1 : ℤ) ^ j * (k.choose j : ℤ) * ((k - j : ℤ) ^ n) : ℤ) : ℚ) =
      ∑ j ∈ range (k + 1),
        ((-1 : ℚ) ^ j * (k.choose j : ℚ) * ((k - j : ℚ) ^ n)) by
    simp]
  let f : ℕ → ℚ :=
    fun m => (-1 : ℚ) ^ (k - m) * (k.choose (k - m) : ℚ) * (m : ℚ) ^ n
  calc
    (∑ j ∈ range (k + 1), (-1 : ℚ) ^ j * (k.choose j : ℚ) * ((k - j : ℚ) ^ n))
        = ∑ j ∈ range (k + 1), f (k + 1 - 1 - j) := by
          apply Finset.sum_congr rfl
          intro j hj
          have hjle : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
          have hsub : k - (k - j) = j := by omega
          rw [show k + 1 - 1 - j = k - j by omega]
          dsimp [f]
          rw [hsub]
          rw [← Nat.cast_sub hjle]
    _ = ∑ m ∈ range (k + 1), f m := Finset.sum_range_reflect f (k + 1)
    _ = ∑ m ∈ range (k + 1),
          (-1 : ℚ) ^ (k - m) * (k.choose m : ℚ) * (m : ℚ) ^ n := by
          apply Finset.sum_congr rfl
          intro m hm
          have hmle : m ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hm)
          dsimp [f]
          rw [Nat.choose_symm hmle]

private lemma coeff_exp_sub_one_pow_sum (n k : ℕ) :
    coeff n (((PowerSeries.exp ℚ) - 1) ^ k) =
      ∑ m ∈ Finset.range (k + 1),
        (-1 : ℚ) ^ (k - m) * (k.choose m : ℚ) * ((m : ℚ) ^ n / n.factorial) := by
  rw [sub_eq_add_neg, add_pow]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro m _hm
  rw [show ((-1 : PowerSeries ℚ) ^ (k - m)) = PowerSeries.C ((-1 : ℚ) ^ (k - m)) by
    simp]
  rw [show ((k.choose m : PowerSeries ℚ)) = PowerSeries.C (k.choose m : ℚ) by
    simp]
  rw [mul_assoc]
  rw [show PowerSeries.C ((-1 : ℚ) ^ (k - m)) * PowerSeries.C (k.choose m : ℚ) =
      PowerSeries.C (((-1 : ℚ) ^ (k - m)) * (k.choose m : ℚ)) by
    simp]
  rw [PowerSeries.coeff_mul_C]
  rw [coeff_exp_pow_eq_pow_div_factorial]
  ring

theorem surjCount_egf_coeff (n k : ℕ) :
    (surjCount n k : ℚ) / n.factorial =
      coeff n (((PowerSeries.exp ℚ) - 1) ^ k) := by
  rw [surjCount_cast_eq_reflected, coeff_exp_sub_one_pow_sum]
  rw [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m _hm
  ring

private lemma derivative_exp_sub_one :
    d⁄dX ℚ (PowerSeries.exp ℚ - 1) = PowerSeries.exp ℚ := by
  ext n
  rw [PowerSeries.coeff_derivative, map_sub, PowerSeries.coeff_exp, PowerSeries.coeff_exp,
    PowerSeries.coeff_one]
  simp
  rw [Nat.factorial_succ]
  norm_num
  field_simp [Nat.cast_ne_zero.mpr n.factorial_pos.ne']

private lemma derivative_exp_sub_one_pow_succ (k : ℕ) :
    d⁄dX ℚ ((PowerSeries.exp ℚ - 1) ^ (k + 1)) =
      ((k + 1 : ℕ) : PowerSeries ℚ) *
        ((PowerSeries.exp ℚ - 1) ^ (k + 1) + (PowerSeries.exp ℚ - 1) ^ k) := by
  rw [PowerSeries.derivative_pow, derivative_exp_sub_one]
  rw [show PowerSeries.exp ℚ = (PowerSeries.exp ℚ - 1) + 1 by ring]
  simp [pow_succ]
  ring

private lemma coeff_derivative_exp_sub_one_pow_succ (n k : ℕ) :
    coeff n (d⁄dX ℚ ((PowerSeries.exp ℚ - 1) ^ (k + 1))) =
      (k + 1 : ℚ) *
        (coeff n ((PowerSeries.exp ℚ - 1) ^ (k + 1)) +
          coeff n ((PowerSeries.exp ℚ - 1) ^ k)) := by
  rw [derivative_exp_sub_one_pow_succ]
  rw [show ((k + 1 : ℕ) : PowerSeries ℚ) = PowerSeries.C ((k + 1 : ℕ) : ℚ) by
    ext t
    cases t <;> simp]
  rw [PowerSeries.coeff_C_mul, map_add]
  norm_num

private lemma exp_sub_one_constantCoeff_zero :
    (PowerSeries.exp ℚ - 1 : PowerSeries ℚ).constantCoeff = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, map_sub, PowerSeries.coeff_exp,
    PowerSeries.coeff_one]
  norm_num

private lemma coeff_pow_eq_zero_of_constantCoeff_eq_zero {f : PowerSeries ℚ}
    (h0 : f.constantCoeff = 0) {n k : ℕ} (hnk : n < k) : coeff n (f ^ k) = 0 := by
  exact PowerSeries.coeff_of_lt_order n
    (lt_of_lt_of_le (by exact_mod_cast hnk)
      (PowerSeries.le_order_pow_of_constantCoeff_eq_zero k h0))

theorem coeff_exp_sub_one_pow_eq_factorial_mul_stirlingSecond (n k : ℕ) :
    coeff n ((PowerSeries.exp ℚ - 1) ^ k) =
      (((k.factorial * Nat.stirlingSecond n k : ℕ) : ℚ) / n.factorial) := by
  revert k
  induction n with
  | zero =>
      intro k
      cases k with
      | zero =>
          simp [Nat.stirlingSecond_zero]
      | succ k =>
          rw [coeff_pow_eq_zero_of_constantCoeff_eq_zero exp_sub_one_constantCoeff_zero
            (show 0 < k + 1 by omega)]
          simp [Nat.stirlingSecond_zero_succ]
  | succ n ih =>
      intro k
      cases k with
      | zero =>
          simp [Nat.stirlingSecond_succ_zero]
      | succ k =>
          have hderiv := coeff_derivative_exp_sub_one_pow_succ n k
          rw [PowerSeries.coeff_derivative] at hderiv
          rw [ih (k + 1), ih k] at hderiv
          apply mul_right_cancel₀ (show (n : ℚ) + 1 ≠ 0 by positivity)
          calc
            coeff (n + 1) ((PowerSeries.exp ℚ - 1) ^ (k + 1)) * ((n : ℚ) + 1)
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

theorem surjCount_eq_factorial_mul_stirlingSecond (n k : ℕ) :
    surjCount n k = ((k.factorial * Nat.stirlingSecond n k : ℕ) : ℤ) := by
  have h := surjCount_egf_coeff n k
  rw [coeff_exp_sub_one_pow_eq_factorial_mul_stirlingSecond] at h
  field_simp [Nat.cast_ne_zero.mpr n.factorial_pos.ne'] at h
  exact_mod_cast h

private lemma exp_sub_one_eq_shift_mul_X :
    (PowerSeries.exp ℚ - 1 : PowerSeries ℚ) =
      (PowerSeries.mk fun p => coeff (p + 1) (PowerSeries.exp ℚ)) * PowerSeries.X := by
  ext n
  cases n with
  | zero => simp [PowerSeries.coeff_exp]
  | succ n => simp [PowerSeries.coeff_exp]

private lemma coeff_exp_sub_one_pow_self (n : ℕ) :
    coeff n (((PowerSeries.exp ℚ) - 1) ^ n) = 1 := by
  let g : PowerSeries ℚ := PowerSeries.mk fun p => coeff (p + 1) (PowerSeries.exp ℚ)
  have hg0 : coeff 0 g = 1 := by
    dsimp [g]
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_exp]
    norm_num
  rw [exp_sub_one_eq_shift_mul_X]
  change coeff n ((g * PowerSeries.X) ^ n) = 1
  rw [show (g * PowerSeries.X) ^ n = g ^ n * PowerSeries.X ^ n by rw [mul_pow]]
  have hcoeff : coeff n (g ^ n * PowerSeries.X ^ n) = coeff 0 (g ^ n) := by
    simpa only [zero_add] using (PowerSeries.coeff_mul_X_pow (g ^ n) n 0)
  rw [hcoeff]
  rw [show coeff 0 (g ^ n) = (coeff 0 g) ^ n by
    simp [PowerSeries.coeff_zero_eq_constantCoeff]]
  simp [hg0]

theorem surjCount_self (n : ℕ) :
    surjCount n n = n.factorial := by
  have h := surjCount_egf_coeff n n
  rw [coeff_exp_sub_one_pow_self] at h
  field_simp [Nat.cast_ne_zero.mpr n.factorial_pos.ne'] at h
  exact_mod_cast h

example : surjCount 1 1 = 1 := by native_decide
example : surjCount 2 1 = 1 := by native_decide
example : surjCount 2 2 = 2 := by native_decide
example : surjCount 3 2 = 6 := by native_decide
example : surjCount 3 3 = 6 := by native_decide
example : surjCount 4 2 = 14 := by native_decide
example : surjCount 4 3 = 36 := by native_decide

theorem surjCount_matches_example : surjCount 4 3 = 36 := by native_decide

/-- Ordered Bell / Fubini number: total ordered set partitions of an `n`-set. -/
def fubiniNumber (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), surjCount n k

example : fubiniNumber 0 = 1 := by native_decide
example : fubiniNumber 1 = 1 := by native_decide
example : fubiniNumber 2 = 3 := by native_decide
example : fubiniNumber 3 = 13 := by native_decide
example : fubiniNumber 4 = 75 := by native_decide
