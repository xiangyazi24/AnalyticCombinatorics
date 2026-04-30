/-
  Analytic Combinatorics — Part A: Symbolic Method
  Chapter II: Labelled Structures and Exponential Generating Functions

  In the labelled universe, atoms carry distinct labels (e.g., the integers
  1..n inside a size-n object). The "labelled product" of two classes A, B
  produces objects of size k+l = n by relabelling their disjoint atoms with
  a chosen partition: the number of such relabellings is `n choose k`. Hence

    (A ⋆ B)_n = ∑_{k+l=n} (n choose k) · A_k · B_l

  Translated to EGFs (where coefficients carry an n! factor),
  the labelled product corresponds to ordinary EGF multiplication:

    EGF(A ⋆ B)(z) = EGF(A)(z) · EGF(B)(z)

  This file formalizes the count and EGF identities for the labelled product
  abstractly, without constructing labelled-object types.

  Reference: F&S Chapter II § II.1–II.2, Theorem II.1.
-/
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass

open PowerSeries

namespace CombinatorialClass

variable (A B : CombinatorialClass)

/-- The count of the labelled product: ∑_{k+l=n} (n choose k) · A_k · B_l. -/
noncomputable def labelProdCount (n : ℕ) : ℕ :=
  ∑ p ∈ Finset.antidiagonal n, n.choose p.1 * (A.count p.1 * B.count p.2)

/-- The EGF of the labelled product equals the product of the EGFs.
    Stated coefficient-wise: (labelProdCount n : ℚ) / n! = [zⁿ] (A.egf · B.egf). -/
theorem labelProdCount_div_factorial_eq_coeff_mul_egf (n : ℕ) :
    (labelProdCount A B n : ℚ) / n.factorial =
      coeff n (A.egf * B.egf) := by
  rw [coeff_mul, labelProdCount]
  simp only [coeff_egf]
  push_cast
  rw [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have hsum : p.1 + p.2 = n := Finset.mem_antidiagonal.mp hp
  have hp1 : p.1 ≤ n := by omega
  have h_npp : n - p.1 = p.2 := by omega
  -- Key factorial identity: n.choose p.1 * p.1! * p.2! = n!
  have hkey_nat : n.choose p.1 * p.1.factorial * p.2.factorial = n.factorial := by
    have := Nat.choose_mul_factorial_mul_factorial hp1
    rwa [h_npp] at this
  have hkey : (n.choose p.1 : ℚ) * (p.1.factorial : ℚ) * (p.2.factorial : ℚ)
              = (n.factorial : ℚ) := by
    exact_mod_cast hkey_nat
  have h_p1_ne : (p.1.factorial : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr p.1.factorial_pos.ne'
  have h_p2_ne : (p.2.factorial : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr p.2.factorial_pos.ne'
  have h_n_ne : (n.factorial : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr n.factorial_pos.ne'
  -- Goal: (n.choose p.1 * (A.count p.1 * B.count p.2)) * (n.factorial)⁻¹
  --     = (A.count p.1 / p.1.factorial) * (B.count p.2 / p.2.factorial)
  rw [show (A.count p.1 : ℚ) / p.1.factorial * ((B.count p.2 : ℚ) / p.2.factorial)
        = ((A.count p.1 : ℚ) * (B.count p.2)) / ((p.1.factorial : ℚ) * p.2.factorial) from by
      rw [div_mul_div_comm]]
  rw [show (n.choose p.1 : ℚ) * ((A.count p.1 : ℚ) * (B.count p.2 : ℚ)) * ((n.factorial : ℚ))⁻¹
        = ((n.choose p.1 : ℚ) * (A.count p.1 * B.count p.2)) / n.factorial from by
      rw [div_eq_mul_inv]]
  rw [div_eq_div_iff h_n_ne (mul_ne_zero h_p1_ne h_p2_ne)]
  linear_combination ((A.count p.1 : ℚ) * (B.count p.2 : ℚ)) * hkey

end CombinatorialClass

/-! ## Worked example: the "set" / "exponential" class

A combinatorial class with exactly one object of each size; its EGF is
`exp(z) = ∑ zⁿ/n!`. Combinatorially, this is the labelled "atomic set" —
each size class has a single labelled representative. -/

/-- The class with a single labelled representative at every size:
    one object of each size n ≥ 0. -/
def singletonClass : CombinatorialClass where
  Obj := ℕ
  size := id
  finite_level n := by
    apply Set.Finite.subset (Set.finite_singleton n)
    intro m hm
    simp only [Set.mem_setOf_eq] at hm
    exact hm

namespace singletonClass

/-- Each level set is the singleton `{n}`. -/
private lemma level_eq_singleton (n : ℕ) :
    singletonClass.level n = ({n} : Finset ℕ) := by
  ext m
  refine ⟨fun hm => ?_, fun hm => ?_⟩
  · have hsz := (CombinatorialClass.level_mem_iff (C := singletonClass) m).mp hm
    exact Finset.mem_singleton.mpr hsz
  · apply (CombinatorialClass.level_mem_iff (C := singletonClass) m).mpr
    exact Finset.mem_singleton.mp hm

/-- Each level has count 1. -/
theorem count_eq_one (n : ℕ) : singletonClass.count n = 1 := by
  show (singletonClass.level n).card = 1
  rw [level_eq_singleton]
  rfl

end singletonClass

/-- The EGF of the singleton class is the exponential power series. -/
theorem singletonClass_egf_eq_exp :
    singletonClass.egf = PowerSeries.exp ℚ := by
  ext n
  rw [CombinatorialClass.coeff_egf, singletonClass.count_eq_one, PowerSeries.coeff_exp]
  simp
