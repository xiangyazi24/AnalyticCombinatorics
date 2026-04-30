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
import Mathlib.Data.Fintype.Perm
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

/-! ## Unit and zero identities for the labelled product. -/

/-- `Epsilon.count 0 = 1` (only the unique size-0 object). -/
theorem Epsilon_count_zero : Epsilon.count 0 = 1 := by
  show (Epsilon.level 0).card = 1
  rw [Finset.card_eq_one]
  refine ⟨(), ?_⟩
  ext x
  refine ⟨fun _ => Finset.mem_singleton_self _, fun _ => ?_⟩
  apply (level_mem_iff (C := Epsilon) x).mpr
  show (0 : ℕ) = 0
  rfl

/-- For `k ≥ 1`, `Epsilon.count k = 0` (no size-k object since Epsilon size = 0). -/
theorem Epsilon_count_pos {k : ℕ} (hk : 0 < k) : Epsilon.count k = 0 := by
  show (Epsilon.level k).card = 0
  rw [Finset.card_eq_zero]
  ext x
  refine ⟨fun hx => ?_, fun hx => absurd hx (Finset.notMem_empty _)⟩
  have hsz : Epsilon.size x = k := (level_mem_iff (C := Epsilon) x).mp hx
  change (0 : ℕ) = k at hsz
  omega

/-- Left unit for the labelled product: `Epsilon ⋆ A` has the same count as `A`. -/
theorem Epsilon_labelProdCount (A : CombinatorialClass) (n : ℕ) :
    labelProdCount Epsilon A n = A.count n := by
  rw [labelProdCount]
  rw [Finset.sum_eq_single (0, n)]
  · -- main term: n.choose 0 * Epsilon.count 0 * A.count n = 1 * 1 * count = count
    rw [Nat.choose_zero_right, Epsilon_count_zero, one_mul, one_mul]
  · -- other terms vanish
    rintro ⟨k, j⟩ hkj hne
    rw [Finset.mem_antidiagonal] at hkj
    have hk : k ≠ 0 := by
      intro h
      subst h
      have : j = n := by omega
      exact hne (by simp [this])
    rw [Epsilon_count_pos (Nat.pos_of_ne_zero hk), zero_mul, mul_zero]
  · -- (0, n) is in antidiagonal n
    intro h
    exfalso
    apply h
    rw [Finset.mem_antidiagonal]
    omega

/-- Right unit for the labelled product: `A ⋆ Epsilon` has the same count as `A`. -/
theorem labelProdCount_Epsilon (A : CombinatorialClass) (n : ℕ) :
    labelProdCount A Epsilon n = A.count n := by
  rw [labelProdCount]
  rw [Finset.sum_eq_single (n, 0)]
  · -- main term: n.choose n * (A.count n * Epsilon.count 0) = 1 · (count · 1) = count
    simp [Nat.choose_self, Epsilon_count_zero]
  · -- other terms vanish
    rintro ⟨k, j⟩ hkj hne
    rw [Finset.mem_antidiagonal] at hkj
    have hj : j ≠ 0 := by
      intro h
      subst h
      have : k = n := by omega
      exact hne (by simp [this])
    rw [Epsilon_count_pos (Nat.pos_of_ne_zero hj)]
    simp
  · intro h
    exfalso
    apply h
    rw [Finset.mem_antidiagonal]
    omega

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

/-! ## Corollaries: connecting our examples through Mathlib's `exp`. -/

/-- The disjoint union of two singleton classes has EGF `2 · exp(z)`. -/
theorem singletonClass_disjSum_egf :
    (singletonClass.disjSum singletonClass).egf = 2 * PowerSeries.exp ℚ := by
  rw [CombinatorialClass.disjSum_egf, singletonClass_egf_eq_exp, two_mul]

/-- The labelled product of singleton with itself, divided by n!, is exp · exp coefficient. -/
theorem singletonClass_labelProdCount_eq (n : ℕ) :
    (CombinatorialClass.labelProdCount singletonClass singletonClass n : ℚ) / n.factorial
      = coeff n (PowerSeries.exp ℚ * PowerSeries.exp ℚ) := by
  rw [CombinatorialClass.labelProdCount_div_factorial_eq_coeff_mul_egf]
  rw [singletonClass_egf_eq_exp]

/-- The labelled product of singleton with itself counts to 2ⁿ at level n.
    Combinatorial reading: a "2-coloured labelled set" of size n is one of 2ⁿ subsets. -/
theorem singletonClass_labelProdCount_pow (n : ℕ) :
    CombinatorialClass.labelProdCount singletonClass singletonClass n = 2 ^ n := by
  rw [CombinatorialClass.labelProdCount]
  simp only [singletonClass.count_eq_one, mul_one]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun k _ => n.choose k) n,
      Nat.sum_range_choose]

/-- Closed form: `[zⁿ] (exp(z))² = 2ⁿ / n!`.
    Derived combinatorially via the labelled-product / singleton identification. -/
theorem coeff_exp_sq_eq_pow_div_factorial (n : ℕ) :
    coeff n (PowerSeries.exp ℚ * PowerSeries.exp ℚ) = (2 ^ n : ℚ) / n.factorial := by
  rw [← singletonClass_labelProdCount_eq, singletonClass_labelProdCount_pow]
  push_cast
  rfl

/-! ## Permutations -/

/-- The class of permutations: at size `n`, the objects are bijections of `Fin n`. -/
def permClass : CombinatorialClass where
  Obj := Σ n : ℕ, Equiv.Perm (Fin n)
  size := Sigma.fst
  finite_level n := by
    have hfin : Set.Finite (Set.univ : Set (Equiv.Perm (Fin n))) := Set.toFinite _
    apply Set.Finite.subset (hfin.image (Sigma.mk n))
    rintro ⟨k, σ⟩ hkσ
    simp only [Set.mem_setOf_eq] at hkσ
    change k = n at hkσ
    subst k
    exact ⟨σ, Set.mem_univ _, rfl⟩

namespace permClass

/-- Count of permutations of size `n` equals `n!`. -/
theorem count_eq_factorial (n : ℕ) : permClass.count n = n.factorial := by
  rw [CombinatorialClass.count]
  have hcard : (permClass.level n).card =
      (Finset.univ : Finset (Equiv.Perm (Fin n))).card := by
    refine Finset.card_bij'
      (s := permClass.level n)
      (t := (Finset.univ : Finset (Equiv.Perm (Fin n))))
      (fun x hx => by
        obtain ⟨k, σ⟩ := x
        have hsize : permClass.size ⟨k, σ⟩ = n :=
          (CombinatorialClass.level_mem_iff (C := permClass) ⟨k, σ⟩).mp hx
        change k = n at hsize
        subst k
        exact σ)
      (fun σ _ => (⟨n, σ⟩ : permClass.Obj))
      ?_ ?_ ?_ ?_
    · intro _ _
      exact Finset.mem_univ _
    · intro σ _
      exact (CombinatorialClass.level_mem_iff (C := permClass) ⟨n, σ⟩).mpr rfl
    · intro x hx
      obtain ⟨k, σ⟩ := x
      have hsize : permClass.size ⟨k, σ⟩ = n :=
        (CombinatorialClass.level_mem_iff (C := permClass) ⟨k, σ⟩).mp hx
      change k = n at hsize
      subst k
      rfl
    · intro σ _
      rfl
  rw [hcard, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]

end permClass

/-- Count of permutations of size `n` equals `n!`. -/
theorem permClass_count_eq_factorial (n : ℕ) : permClass.count n = n.factorial :=
  permClass.count_eq_factorial n

/-- Every coefficient of `permClass.egf` equals 1. -/
theorem permClass_egf_coeff (n : ℕ) : coeff n permClass.egf = 1 := by
  rw [CombinatorialClass.coeff_egf, permClass_count_eq_factorial]
  exact div_self (Nat.cast_ne_zero.mpr n.factorial_pos.ne')
