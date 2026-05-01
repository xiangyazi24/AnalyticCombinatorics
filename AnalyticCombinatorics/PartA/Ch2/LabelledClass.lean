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
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Powerset
import Mathlib.Topology.Instances.Rat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass
import AnalyticCombinatorics.PartA.Ch3.Parameters

set_option linter.style.show false

open PowerSeries
open scoped PowerSeries.WithPiTopology

namespace CombinatorialClass

variable (A B : CombinatorialClass)

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

/-- `[zⁿ] (exp z)^k = k^n / n!`. Generalizes `coeff_exp_sq` (`k = 2`). -/
theorem coeff_exp_pow_eq_pow_div_factorial (k n : ℕ) :
    coeff n ((PowerSeries.exp ℚ) ^ k) = (k ^ n : ℚ) / n.factorial := by
  rw [PowerSeries.exp_pow_eq_rescale_exp (A := ℚ) k]
  simp [PowerSeries.coeff_rescale, PowerSeries.coeff_exp, div_eq_mul_inv]

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

/-- The EGF of permutations is the geometric series `1 + z + z² + ⋯`. -/
theorem permClass_egf_eq_mk_one :
    permClass.egf = (PowerSeries.mk fun _ : ℕ => (1 : ℚ)) := by
  ext n
  rw [permClass_egf_coeff, PowerSeries.coeff_mk]

/-- The permutation EGF satisfies the geometric-series identity. -/
theorem permClass_egf_mul_one_sub_X :
    permClass.egf * (1 - PowerSeries.X) = 1 := by
  rw [permClass_egf_eq_mk_one]
  exact PowerSeries.mk_one_mul_one_sub_eq_one ℚ

/-- For `(n, σ) ∈ permClass`, the number of fixed points of `σ`. -/
noncomputable def permClass.numFixedPoints :
    Parameter permClass :=
  fun s => (Finset.univ.filter (fun i : Fin s.fst => s.snd i = i)).card

/-- Sanity: the empty permutation has all zero of its points fixed. -/
example : permClass.jointCount permClass.numFixedPoints 0 0 = 1 := by
  rw [CombinatorialClass.jointCount]
  have hfilter :
      (permClass.level 0).filter (fun a => permClass.numFixedPoints a = 0) =
        permClass.level 0 := by
    apply Finset.filter_true_of_mem
    intro a ha
    obtain ⟨n, σ⟩ := a
    have hn : n = 0 :=
      (CombinatorialClass.level_mem_iff (C := permClass) ⟨n, σ⟩).mp ha
    subst n
    simp [permClass.numFixedPoints]
  rw [hfilter]
  rw [← CombinatorialClass.count, permClass_count_eq_factorial]
  rfl

/-- Sanity: the unique permutation of one point fixes that point. -/
example : permClass.jointCount permClass.numFixedPoints 1 1 = 1 := by
  rw [CombinatorialClass.jointCount]
  have hfilter :
      (permClass.level 1).filter (fun a => permClass.numFixedPoints a = 1) =
        permClass.level 1 := by
    apply Finset.filter_true_of_mem
    intro a ha
    obtain ⟨n, σ⟩ := a
    have hn : n = 1 :=
      (CombinatorialClass.level_mem_iff (C := permClass) ⟨n, σ⟩).mp ha
    subst n
    rw [permClass.numFixedPoints]
    have hfixed :
        (Finset.univ.filter (fun i : Fin 1 => σ i = i)) = Finset.univ := by
      apply Finset.filter_true_of_mem
      intro i _
      exact Subsingleton.elim (σ i) i
    rw [hfixed, Finset.card_univ, Fintype.card_fin]
  rw [hfilter]
  rw [← CombinatorialClass.count, permClass_count_eq_factorial]
  rfl

namespace CombinatorialClass

private abbrev LabelProdFiber (A B : CombinatorialClass) (p : ℕ × ℕ) : Type :=
  ((A.level p.1) × (B.level p.2)) ×
    ((Finset.univ : Finset (Fin (p.1 + p.2))).powersetCard p.1)

private noncomputable def labelProdFiberFinset (A B : CombinatorialClass) (p : ℕ × ℕ) :
    Finset (LabelProdFiber A B p) :=
  ((A.level p.1).attach ×ˢ (B.level p.2).attach) ×ˢ
    (((Finset.univ : Finset (Fin (p.1 + p.2))).powersetCard p.1).attach)

private noncomputable def labelProdLevelFinset (A B : CombinatorialClass) (n : ℕ) :
    Finset (Σ p : ℕ × ℕ, LabelProdFiber A B p) :=
  (Finset.antidiagonal n).sigma (labelProdFiberFinset A B)

private lemma mem_labelProdLevelFinset_iff
    (A B : CombinatorialClass) (n : ℕ) (x : Σ p : ℕ × ℕ, LabelProdFiber A B p) :
    x ∈ labelProdLevelFinset A B n ↔ x.1.1 + x.1.2 = n := by
  cases x with
  | mk p y =>
      rcases y with ⟨⟨a, b⟩, S⟩
      simp [labelProdLevelFinset, labelProdFiberFinset, LabelProdFiber]

/-- The labelled product class. An object records sizes `k,m`, one object from each
level, and a `k`-element subset of the `k+m` labels assigned to the left factor. -/
noncomputable def labelProd (A B : CombinatorialClass) : CombinatorialClass where
  Obj := Σ p : ℕ × ℕ, LabelProdFiber A B p
  size := fun x => x.1.1 + x.1.2
  finite_level n := by
    exact (labelProdLevelFinset A B n).finite_toSet.subset fun x hx =>
      (mem_labelProdLevelFinset_iff A B n x).mpr hx

/-- The object-level labelled product has the abstract labelled-product count. -/
theorem labelProd_count_eq_labelProdCount (A B : CombinatorialClass) (n : ℕ) :
    (A.labelProd B).count n = labelProdCount A B n := by
  rw [count]
  have hlevel : (A.labelProd B).level n = labelProdLevelFinset A B n := by
    ext x
    rw [level_mem_iff]
    exact (mem_labelProdLevelFinset_iff A B n x).symm
  rw [hlevel, labelProdCount, labelProdLevelFinset]
  calc
    ((Finset.antidiagonal n).sigma (labelProdFiberFinset A B)).card =
        ∑ p ∈ Finset.antidiagonal n, (labelProdFiberFinset A B p).card := by
      exact Finset.card_sigma (s := Finset.antidiagonal n) (t := labelProdFiberFinset A B)
    _ = ∑ p ∈ Finset.antidiagonal n, n.choose p.1 * (A.count p.1 * B.count p.2) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hpn : p.1 + p.2 = n := Finset.mem_antidiagonal.mp hp
      simp [labelProdFiberFinset, count, hpn, Finset.card_product, Finset.card_powersetCard,
        Nat.mul_assoc, Nat.mul_comm]

/-- EGF form of the object-level labelled product. -/
theorem labelProd_egf (A B : CombinatorialClass) :
    (A.labelProd B).egf = A.egf * B.egf := by
  ext n
  rw [coeff_egf, labelProd_count_eq_labelProdCount,
      labelProdCount_div_factorial_eq_coeff_mul_egf]

/-- `k`-fold labelled product of `A` with itself. By convention `labelPow A 0`
is the labelled-product unit `Epsilon`. -/
noncomputable def labelPow : CombinatorialClass → ℕ → CombinatorialClass
  | _, 0 => Epsilon
  | A, k + 1 => A.labelProd (labelPow A k)

/-- The EGF of `labelPow A k` is `A.egf ^ k`. -/
theorem labelPow_egf (A : CombinatorialClass) (k : ℕ) :
    (labelPow A k).egf = A.egf ^ k := by
  induction k with
  | zero =>
      simp [labelPow, Epsilon_egf]
  | succ k ih =>
      simp [labelPow, labelProd_egf, ih, pow_succ']

/-- Coefficient form of the EGF identity for `labelPow`. -/
theorem labelPow_count_div_factorial_eq_coeff_pow
    (A : CombinatorialClass) (k n : ℕ) :
    ((labelPow A k).count n : ℚ) / n.factorial = coeff n (A.egf ^ k) := by
  rw [← coeff_egf (A := labelPow A k), labelPow_egf]

private lemma size_pos_of_count_zero {B : CombinatorialClass} (hB : B.count 0 = 0)
    (b : B.Obj) : 1 ≤ B.size b := by
  rcases Nat.eq_zero_or_pos (B.size b) with h0 | hp
  · exfalso
    have hmem : b ∈ B.level 0 := (level_mem_iff (C := B) b).mpr h0
    have hcard : 0 < B.count 0 := by
      rw [count]
      exact Finset.card_pos.mpr ⟨b, hmem⟩
    omega
  · omega

private lemma labelPow_size_ge (B : CombinatorialClass) (hB : B.count 0 = 0) :
    ∀ (k : ℕ) (x : (labelPow B k).Obj), k ≤ (labelPow B k).size x
  | 0, _ => by simp [labelPow]
  | k + 1, x => by
      rcases x with ⟨p, ⟨⟨b, y⟩, S⟩⟩
      have hb_size : B.size b.1 = p.1 := (level_mem_iff (C := B) b.1).mp b.2
      have hy_size : (labelPow B k).size y.1 = p.2 :=
        (level_mem_iff (C := labelPow B k) y.1).mp y.2
      have hb_pos : 1 ≤ p.1 := by
        rw [← hb_size]
        exact size_pos_of_count_zero hB b.1
      have hy_ge : k ≤ p.2 := by
        rw [← hy_size]
        exact labelPow_size_ge B hB k y.1
      change k + 1 ≤ p.1 + p.2
      omega

private noncomputable def labelSeqLevelFinset
    (B : CombinatorialClass) (_hB : B.count 0 = 0) (n : ℕ) :
    Finset (Σ k : ℕ, (labelPow B k).Obj) :=
  (Finset.range (n + 1)).sigma fun k => (labelPow B k).level n

private lemma mem_labelSeqLevelFinset_iff
    (B : CombinatorialClass) (hB : B.count 0 = 0) (n : ℕ)
    (x : Σ k : ℕ, (labelPow B k).Obj) :
    x ∈ labelSeqLevelFinset B hB n ↔ (labelPow B x.1).size x.2 = n := by
  cases x with
  | mk k y =>
      constructor
      · intro hx
        exact (level_mem_iff (C := labelPow B k) y).mp (Finset.mem_sigma.mp hx).2
      · intro hy
        apply Finset.mem_sigma.mpr
        refine ⟨?_, ?_⟩
        · apply Finset.mem_range.mpr
          have hk := labelPow_size_ge B hB k y
          rw [hy] at hk
          exact Nat.lt_succ_of_le hk
        · exact (level_mem_iff (C := labelPow B k) y).mpr hy

/-- Labelled sequence construction as the disjoint union of all labelled powers. -/
noncomputable def labelSeq (B : CombinatorialClass) (hB : B.count 0 = 0) :
    CombinatorialClass where
  Obj := Σ k : ℕ, (labelPow B k).Obj
  size := fun x => (labelPow B x.1).size x.2
  finite_level n := by
    exact (labelSeqLevelFinset B hB n).finite_toSet.subset fun x hx =>
      (mem_labelSeqLevelFinset_iff B hB n x).mpr hx

namespace labelSeq

/-- Count of `labelSeq` is the finite sum of labelled-power counts. -/
theorem count_eq (B : CombinatorialClass) (hB : B.count 0 = 0) (n : ℕ) :
    (labelSeq B hB).count n =
      ∑ k ∈ Finset.range (n + 1), (labelPow B k).count n := by
  rw [count]
  have hlevel : (labelSeq B hB).level n = labelSeqLevelFinset B hB n := by
    ext x
    rw [level_mem_iff]
    exact (mem_labelSeqLevelFinset_iff B hB n x).symm
  rw [hlevel, labelSeqLevelFinset]
  exact Finset.card_sigma (s := Finset.range (n + 1)) (t := fun k => (labelPow B k).level n)

end labelSeq

private lemma coeff_pow_eq_zero_of_constantCoeff_eq_zero {f : PowerSeries ℚ}
    (h0 : f.constantCoeff = 0) {n k : ℕ} (hnk : n < k) : coeff n (f ^ k) = 0 := by
  exact PowerSeries.coeff_of_lt_order n
    (lt_of_lt_of_le (by exact_mod_cast hnk)
      (PowerSeries.le_order_pow_of_constantCoeff_eq_zero k h0))

private lemma egf_constantCoeff_eq_zero (B : CombinatorialClass) (hB : B.count 0 = 0) :
    B.egf.constantCoeff = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_egf, hB]
  simp

private lemma labelSeq_coeff_egf (B : CombinatorialClass) (hB : B.count 0 = 0) (n : ℕ) :
    coeff n (labelSeq B hB).egf =
      ∑ k ∈ Finset.range (n + 1), coeff n (B.egf ^ k) := by
  rw [coeff_egf, labelSeq.count_eq]
  rw [Nat.cast_sum, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  rw [← div_eq_mul_inv]
  exact labelPow_count_div_factorial_eq_coeff_pow B k n

private lemma labelSeq_hasSum_egf (B : CombinatorialClass) (hB : B.count 0 = 0) :
    HasSum (fun k : ℕ => B.egf ^ k) (labelSeq B hB).egf := by
  rw [PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff]
  intro n
  rw [labelSeq_coeff_egf B hB n]
  apply hasSum_sum_of_ne_finset_zero (s := Finset.range (n + 1))
  intro k hk
  have hnk : n < k := by
    have hk' : ¬ k < n + 1 := by simpa using hk
    omega
  exact coeff_pow_eq_zero_of_constantCoeff_eq_zero (egf_constantCoeff_eq_zero B hB) hnk

/-- The EGF of labelled sequences satisfies the geometric-series identity. -/
theorem labelSeq_egf_mul_one_sub_egf (B : CombinatorialClass) (hB : B.count 0 = 0) :
    (1 - B.egf) * (labelSeq B hB).egf = 1 := by
  rw [← (labelSeq_hasSum_egf B hB).tsum_eq]
  exact PowerSeries.WithPiTopology.one_sub_mul_tsum_pow_of_constantCoeff_eq_zero
    (egf_constantCoeff_eq_zero B hB)

/-- Labelled SET coefficient, as a rational unordered-block count. -/
noncomputable def labelSetCount (B : CombinatorialClass) (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1), ((labelPow B k).count n : ℚ) / k.factorial

/-- Coefficient form of the labelled SET partial exponential identity. -/
theorem labelSetCount_div_factorial_eq_partial_exp_coeff
    (B : CombinatorialClass) (n : ℕ) :
    labelSetCount B n / n.factorial =
      ∑ k ∈ Finset.range (n + 1), coeff n ((B.egf : PowerSeries ℚ) ^ k) / k.factorial := by
  rw [labelSetCount, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  rw [← labelPow_count_div_factorial_eq_coeff_pow B k n]
  field_simp [Nat.cast_ne_zero.mpr k.factorial_pos.ne',
    Nat.cast_ne_zero.mpr n.factorial_pos.ne']

end CombinatorialClass

/-! Sanity checks: concrete factorial counts for permutations. -/
example : permClass.count 0 = 1 := by rw [permClass_count_eq_factorial]; rfl
example : permClass.count 1 = 1 := by rw [permClass_count_eq_factorial]; rfl
example : permClass.count 2 = 2 := by rw [permClass_count_eq_factorial]; rfl
example : permClass.count 3 = 6 := by rw [permClass_count_eq_factorial]; rfl
example : permClass.count 4 = 24 := by rw [permClass_count_eq_factorial]; rfl
example : permClass.count 5 = 120 := by rw [permClass_count_eq_factorial]; rfl
example : permClass.count 6 = 720 := by rw [permClass_count_eq_factorial]; rfl
example : permClass.count 7 = 5040 := by rw [permClass_count_eq_factorial]; rfl

/-! Sanity examples for `permClass` via the EGF coefficient identity. -/
example : (PowerSeries.coeff 0 permClass.egf : ℚ) = 1 := permClass_egf_coeff 0
example : (PowerSeries.coeff 5 permClass.egf : ℚ) = 1 := permClass_egf_coeff 5

example : CombinatorialClass.labelProdCount singletonClass singletonClass 3 = 8 :=
  singletonClass_labelProdCount_pow 3
example : CombinatorialClass.labelProdCount singletonClass singletonClass 5 = 32 :=
  singletonClass_labelProdCount_pow 5

namespace CombinatorialClass

/-- Atom has no size-0 element. -/
theorem Atom_count_zero : Atom.count 0 = 0 := by
  change (Atom.level 0).card = 0
  rw [Finset.card_eq_zero]
  ext x
  simp only [Finset.notMem_empty, iff_false]
  intro hx
  have := (CombinatorialClass.level_mem_iff (C := Atom) x).mp hx
  change (1 : ℕ) = 0 at this
  exact one_ne_zero this

/-- Iterated labelled product of Atom: count is k! · δ_{k,n}. -/
theorem labelPow_Atom_count (k n : ℕ) :
    (CombinatorialClass.labelPow Atom k).count n = if n = k then n.factorial else 0 := by
  have hcoeff := CombinatorialClass.labelPow_count_div_factorial_eq_coeff_pow Atom k n
  rw [CombinatorialClass.Atom_egf, PowerSeries.coeff_X_pow] at hcoeff
  by_cases hnk : n = k
  · subst n
    simp only [if_true] at hcoeff ⊢
    field_simp [Nat.cast_ne_zero.mpr k.factorial_pos.ne'] at hcoeff
    exact_mod_cast hcoeff
  · simp only [if_false, hnk] at hcoeff ⊢
    field_simp [Nat.cast_ne_zero.mpr n.factorial_pos.ne'] at hcoeff
    rw [mul_zero] at hcoeff
    exact Nat.cast_eq_zero.mp hcoeff

/-- The labelled SET of Atom has constant count 1 at every size. -/
theorem labelSetCount_Atom (n : ℕ) :
    CombinatorialClass.labelSetCount Atom n = 1 := by
  rw [CombinatorialClass.labelSetCount]
  rw [Finset.sum_eq_single n]
  · rw [CombinatorialClass.labelPow_Atom_count n n, if_pos rfl]
    exact div_self (Nat.cast_ne_zero.mpr n.factorial_pos.ne')
  · intro k _ hkn
    rw [CombinatorialClass.labelPow_Atom_count k n, if_neg (Ne.symm hkn)]
    simp
  · intro hn
    exfalso
    exact hn (Finset.mem_range.mpr (Nat.lt_succ_self n))

end CombinatorialClass

namespace CombinatorialClass

/-- Labelled CYC coefficient (rational): the number of labelled cycles
    of B-objects of total size n, where each k-cycle is counted with
    weight 1/k (since cyclic rotations of a k-tuple represent the same cycle). -/
noncomputable def labelCycCount (B : CombinatorialClass) (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1), if k = 0 then 0 else
    ((labelPow B k).count n : ℚ) / (k : ℚ)

/-- The labelled CYC count divided by n! equals the partial-log coefficient. -/
theorem labelCycCount_div_factorial_eq_partial_log_coeff
    (B : CombinatorialClass) (n : ℕ) :
    labelCycCount B n / n.factorial =
      ∑ k ∈ Finset.range (n + 1), if k = 0 then 0 else
        coeff n ((B.egf : PowerSeries ℚ) ^ k) / (k : ℚ) := by
  rw [labelCycCount, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k = 0
  · simp [hk]
  · simp only [if_neg hk]
    rw [← labelPow_count_div_factorial_eq_coeff_pow B k n]
    field_simp [Nat.cast_ne_zero.mpr n.factorial_pos.ne', Nat.cast_ne_zero.mpr hk]

/-- `labelCycCount Atom` is zero at size 0. -/
example : labelCycCount Atom 0 = 0 := by
  simp [labelCycCount]

/-- `labelCycCount Atom = (n - 1)!` for positive sizes. -/
theorem labelCycCount_Atom_succ (n : ℕ) :
    labelCycCount Atom (n + 1) = (n.factorial : ℚ) := by
  rw [labelCycCount]
  rw [Finset.sum_eq_single (n + 1)]
  · rw [if_neg (Nat.succ_ne_zero n), CombinatorialClass.labelPow_Atom_count (n + 1) (n + 1),
      if_pos rfl, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add_one]
    field_simp [show ((n : ℚ) + 1) ≠ 0 by positivity]
  · intro k _ hkn
    by_cases hk : k = 0
    · simp [hk]
    · rw [if_neg hk, CombinatorialClass.labelPow_Atom_count k (n + 1),
        if_neg (Ne.symm hkn)]
      simp
  · intro hn
    exfalso
    exact hn (Finset.mem_range.mpr (Nat.lt_succ_self (n + 1)))

example : labelCycCount Atom 1 = 1 := by
  rw [labelCycCount_Atom_succ]
  rfl

example : labelCycCount Atom 2 = 1 := by
  rw [labelCycCount_Atom_succ]
  rfl

example : labelCycCount Atom 3 = 2 := by
  rw [labelCycCount_Atom_succ]
  rfl

example : labelCycCount Atom 4 = 6 := by
  rw [labelCycCount_Atom_succ]
  rfl

/-- labelProd is EGF-associative: `((A ⋆ B) ⋆ C).egf = (A ⋆ (B ⋆ C)).egf`. -/
theorem labelProd_assoc_egf (A B C : CombinatorialClass.{0}) :
    ((A.labelProd B).labelProd C).egf = (A.labelProd (B.labelProd C)).egf := by
  rw [labelProd_egf, labelProd_egf, labelProd_egf, labelProd_egf, mul_assoc]

/-- Symmetry: `A ⋆ B` and `B ⋆ A` have the same EGF. -/
theorem labelProd_comm_egf (A B : CombinatorialClass.{0}) :
    (A.labelProd B).egf = (B.labelProd A).egf := by
  rw [labelProd_egf, labelProd_egf, mul_comm]

/-- labelProdCount is associative at the count level. -/
theorem labelProdCount_assoc (A B C : CombinatorialClass.{0}) (n : ℕ) :
    labelProdCount (A.labelProd B) C n = labelProdCount A (B.labelProd C) n := by
  apply Nat.cast_injective (R := ℚ)
  have h := congrArg (fun f : PowerSeries ℚ => coeff n f) (labelProd_assoc_egf A B C)
  simp only [coeff_egf, labelProd_count_eq_labelProdCount] at h
  have h' := congrArg (fun x : ℚ => x * (n.factorial : ℚ)) h
  field_simp [Nat.cast_ne_zero.mpr n.factorial_pos.ne'] at h'
  exact h'

/-- labelProdCount is symmetric. -/
theorem labelProdCount_comm (A B : CombinatorialClass.{0}) (n : ℕ) :
    labelProdCount A B n = labelProdCount B A n := by
  apply Nat.cast_injective (R := ℚ)
  have h := congrArg (fun f : PowerSeries ℚ => coeff n f) (labelProd_comm_egf A B)
  simp only [coeff_egf, labelProd_count_eq_labelProdCount] at h
  have h' := congrArg (fun x : ℚ => x * (n.factorial : ℚ)) h
  field_simp [Nat.cast_ne_zero.mpr n.factorial_pos.ne'] at h'
  exact h'

/-- Labelled product of `permClass` and `Atom`: EGF `X / (1 - X)`. -/
theorem permClass_labelProd_Atom_egf :
    (permClass.labelProd Atom).egf * (1 - PowerSeries.X) = PowerSeries.X := by
  rw [labelProd_egf, Atom_egf]
  rw [show permClass.egf * PowerSeries.X * (1 - PowerSeries.X)
      = PowerSeries.X * (permClass.egf * (1 - PowerSeries.X)) by ring,
    permClass_egf_mul_one_sub_X, mul_one]

/-- The EGF of `permClass` has constant term `1`. -/
example : PowerSeries.constantCoeff permClass.egf = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, permClass_egf_coeff]

end CombinatorialClass

namespace CombinatorialClass

/-- The labelled SEQ of unit atoms has the same count as permutations: count n = n!. -/
theorem labelSeq_Atom_count (n : ℕ) :
    (CombinatorialClass.labelSeq Atom Atom_count_zero).count n = n.factorial := by
  rw [CombinatorialClass.labelSeq.count_eq]
  rw [Finset.sum_eq_single n]
  · simp [labelPow_Atom_count]
  · intro k _ hk
    rw [labelPow_Atom_count]
    rw [if_neg (Ne.symm hk)]
  · intro h
    exfalso
    apply h
    simp

/-- Therefore labelSeq Atom and permClass have the same count function. -/
example (n : ℕ) :
    (CombinatorialClass.labelSeq Atom Atom_count_zero).count n = permClass.count n := by
  rw [labelSeq_Atom_count, permClass_count_eq_factorial]

example (n : ℕ) :
    permClass.egf.coeff n = 1 := permClass_egf_coeff n

example (n : ℕ) :
    permClass.ogf.coeff n = (n.factorial : ℕ) := by
  rw [coeff_ogf, permClass_count_eq_factorial]

example : permClass.count 8 = 40320 := by
  rw [permClass_count_eq_factorial]
  decide

example : permClass.count 9 = 362880 := by
  rw [permClass_count_eq_factorial]
  decide

example : permClass.count 10 = 3628800 := by
  rw [permClass_count_eq_factorial]
  decide

example : permClass.ogf.coeff 0 = 1 := by
  rw [coeff_ogf, permClass_count_eq_factorial]; rfl

example : permClass.ogf.coeff 3 = 6 := by
  rw [coeff_ogf, permClass_count_eq_factorial]; decide

set_option linter.flexible false in
example : CombinatorialClass.labelProdCount permClass permClass 0 = 1 := by
  unfold CombinatorialClass.labelProdCount
  simp [permClass_count_eq_factorial]

set_option linter.flexible false in
example : CombinatorialClass.labelProdCount permClass permClass 2 = 6 := by
  unfold CombinatorialClass.labelProdCount
  simp [permClass_count_eq_factorial]
  decide

/-- Coefficients of a power of the geometric series, in multichoose form. -/
theorem coeff_mk_one_pow_eq_multichoose (k n : ℕ) :
    coeff n ((PowerSeries.mk fun _ : ℕ => (1 : ℚ)) ^ k) =
      (Nat.multichoose k n : ℚ) := by
  cases k with
  | zero =>
      cases n with
      | zero => simp
      | succ n => simp
  | succ d =>
      change coeff n ((PowerSeries.mk (1 : ℕ → ℚ)) ^ (d + 1)) =
        (Nat.multichoose (d + 1) n : ℚ)
      rw [PowerSeries.mk_one_pow_eq_mk_choose_add]
      simp only [PowerSeries.coeff_mk]
      norm_cast
      rw [Nat.multichoose_eq]
      have h : d + 1 + n - 1 = d + n := by omega
      rw [h, Nat.choose_symm_add]

/-- Count formula for `k` labelled factors of the permutation class. -/
theorem labelPow_permClass_count_multichoose (k n : ℕ) :
    (CombinatorialClass.labelPow permClass k).count n =
      n.factorial * Nat.multichoose k n := by
  apply Nat.cast_injective (R := ℚ)
  have h := CombinatorialClass.labelPow_count_div_factorial_eq_coeff_pow permClass k n
  rw [permClass_egf_eq_mk_one, coeff_mk_one_pow_eq_multichoose] at h
  have h' := congrArg (fun x : ℚ => x * (n.factorial : ℚ)) h
  field_simp [Nat.cast_ne_zero.mpr n.factorial_pos.ne'] at h'
  rw [Nat.cast_mul]
  exact h'

/-- Count formula for `k` labelled factors of the permutation class, as a binomial coefficient. -/
theorem labelPow_permClass_count (k n : ℕ) :
    (CombinatorialClass.labelPow permClass k).count n =
      n.factorial * (n + k - 1).choose n := by
  rw [labelPow_permClass_count_multichoose, Nat.multichoose_eq]
  congr 1
  rw [Nat.add_comm]

set_option linter.flexible false in
example : (CombinatorialClass.labelPow permClass 0).count 0 = 1 := by
  simp [CombinatorialClass.labelPow, Epsilon_count_zero]

set_option linter.flexible false in
example : (CombinatorialClass.labelPow permClass 0).count 1 = 0 := by
  simp [CombinatorialClass.labelPow]
  rw [Epsilon_count_pos (by omega)]

example : (CombinatorialClass.labelPow permClass 1).count 1 = 1 := by
  rw [labelPow_permClass_count]
  rfl

example : (CombinatorialClass.labelPow permClass 2).count 2 = 6 := by
  rw [labelPow_permClass_count]
  decide

example (k n : ℕ) :
    coeff n (permClass.egf ^ k) = (Nat.multichoose k n : ℚ) := by
  rw [← labelPow_egf]
  rw [coeff_egf]
  rw [labelPow_permClass_count_multichoose]
  push_cast
  field_simp

end CombinatorialClass
