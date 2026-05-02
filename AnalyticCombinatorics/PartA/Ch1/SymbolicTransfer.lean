/-
  Analytic Combinatorics — Part A, Chapter I/II

  Showcase transfer statements for the symbolic method: disjoint sum,
  cartesian product, powers, and sequence examples at the counting level.
-/
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass
import AnalyticCombinatorics.PartA.Ch1.Sequences
import Mathlib.Tactic

set_option linter.style.show false
set_option linter.style.nativeDecide false
set_option linter.unusedSimpArgs false

open CombinatorialClass

namespace CombinatorialClass

/-! ## Basic level-count forms -/

/-- The neutral class has one object at size 0 and none elsewhere. -/
theorem Epsilon_count (n : ℕ) :
    Epsilon.count n = if n = 0 then 1 else 0 := by
  simp only [count]
  haveI : Unique Epsilon.Obj := inferInstanceAs (Unique Unit)
  have hmem : ∀ x : Epsilon.Obj, x ∈ Epsilon.level n ↔ n = 0 := fun x => by
    rw [level_mem_iff]
    show (0 : ℕ) = n ↔ n = 0
    omega
  by_cases h : n = 0
  · have hcard : (Epsilon.level n).card = 1 := by
      rw [Finset.card_eq_one]
      exact ⟨(), Finset.eq_singleton_iff_unique_mem.mpr
        ⟨(hmem ()).mpr h, fun x _ => Unique.eq_default x⟩⟩
    rw [hcard]
    simp [h]
  · have hcard : (Epsilon.level n).card = 0 := by
      rw [Finset.card_eq_zero]
      exact Finset.eq_empty_of_forall_notMem (fun x hx => h ((hmem x).mp hx))
    rw [hcard]
    simp [h]

/-- The atom class has one object at size 1 and none elsewhere. -/
theorem Atom_count (n : ℕ) :
    Atom.count n = if n = 1 then 1 else 0 := by
  simp only [count]
  haveI : Unique Atom.Obj := inferInstanceAs (Unique Unit)
  have hmem : ∀ x : Atom.Obj, x ∈ Atom.level n ↔ n = 1 := fun x => by
    rw [level_mem_iff]
    show (1 : ℕ) = n ↔ n = 1
    omega
  by_cases h : n = 1
  · have hcard : (Atom.level n).card = 1 := by
      rw [Finset.card_eq_one]
      exact ⟨(), Finset.eq_singleton_iff_unique_mem.mpr
        ⟨(hmem ()).mpr h, fun x _ => Unique.eq_default x⟩⟩
    rw [hcard]
    simp [h]
  · have hcard : (Atom.level n).card = 0 := by
      rw [Finset.card_eq_zero]
      exact Finset.eq_empty_of_forall_notMem (fun x hx => h ((hmem x).mp hx))
    rw [hcard]
    simp [h]

theorem Atom_count_zero : Atom.count 0 = 0 := by
  rw [Atom_count]
  norm_num

/-! ## Transfer theorems collected from `CombinatorialClass` -/

/-- Disjoint union transfers to addition of counting sequences. -/
theorem disjSum_transfer_count (A B : CombinatorialClass) (n : ℕ) :
    (A.disjSum B).count n = A.count n + B.count n :=
  A.disjSum_count B n

/-- Cartesian product transfers to Cauchy convolution of counting sequences. -/
theorem cartProd_transfer_count (A B : CombinatorialClass) (n : ℕ) :
    (A.cartProd B).count n =
      ∑ p ∈ Finset.antidiagonal n, A.count p.1 * B.count p.2 :=
  A.cartProd_count B n

/-- A worked additive transfer: `Atom + Atom` has two objects of size 1. -/
theorem disjSum_Atom_Atom_count (n : ℕ) :
    (Atom.disjSum Atom).count n = if n = 1 then 2 else 0 := by
  rw [disjSum_transfer_count, Atom_count]
  by_cases h : n = 1 <;> simp [h]

/-! ## Product examples -/

/-- `Atom × Atom` has one object at size 2 and none elsewhere. -/
theorem cartProd_Atom_Atom_count (n : ℕ) :
    (Atom.cartProd Atom).count n = if n = 2 then 1 else 0 := by
  rw [cartProd_transfer_count]
  by_cases hn : n = 2
  · subst n
    rw [Finset.sum_eq_single (1, 1)]
    · simp [Atom_count]
    · rintro ⟨k, m⟩ hkm hne
      rw [Finset.mem_antidiagonal] at hkm
      by_cases hk : k = 1
      · have hm : m = 1 := by omega
        exact (hne (Prod.ext hk hm)).elim
      · simp [Atom_count, hk]
    · intro hmissing
      exfalso
      apply hmissing
      rw [Finset.mem_antidiagonal]
      norm_num
  · rw [Finset.sum_eq_zero]
    · simp [hn]
    · rintro ⟨k, m⟩ hkm
      rw [Finset.mem_antidiagonal] at hkm
      by_cases hk : k = 1
      · have hm : m ≠ 1 := by
          intro hm
          apply hn
          omega
        simp [Atom_count, hk, hm]
      · simp [Atom_count, hk]

example : (Atom.cartProd Atom).count 0 = 0 := by
  rw [cartProd_Atom_Atom_count]
  native_decide

example : (Atom.cartProd Atom).count 1 = 0 := by
  rw [cartProd_Atom_Atom_count]
  native_decide

example : (Atom.cartProd Atom).count 2 = 1 := by
  rw [cartProd_Atom_Atom_count]
  native_decide

example : (Atom.cartProd Atom).count 3 = 0 := by
  rw [cartProd_Atom_Atom_count]
  native_decide

example : (Atom.cartProd Atom).count 4 = 0 := by
  rw [cartProd_Atom_Atom_count]
  native_decide

example : (Atom.cartProd Atom).count 5 = 0 := by
  rw [cartProd_Atom_Atom_count]
  native_decide

/-! ## Powers as iterated products -/

/-- `A^k`, represented recursively as a `k`-fold cartesian product. -/
noncomputable def powClass (A : CombinatorialClass) : ℕ → CombinatorialClass
  | 0 => Epsilon
  | k + 1 => A.cartProd (powClass A k)

/-- The corresponding `k`-fold convolution of a counting sequence. -/
def powCount (a : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, n => if n = 0 then 1 else 0
  | k + 1, n => ∑ p ∈ Finset.antidiagonal n, a p.1 * powCount a k p.2

/-- Iterated products transfer to iterated Cauchy convolution. -/
theorem powClass_count (A : CombinatorialClass) (k n : ℕ) :
    (powClass A k).count n = powCount A.count k n := by
  induction k generalizing n with
  | zero =>
      simp [powClass, powCount, Epsilon_count]
  | succ k ih =>
      simp [powClass, powCount, cartProd_transfer_count, ih]

/-- The `k`-fold convolution of the atom sequence is concentrated at `k`. -/
theorem powCount_Atom_count (k n : ℕ) :
    powCount Atom.count k n = if n = k then 1 else 0 := by
  induction k generalizing n with
  | zero =>
      simp [powCount, Atom_count]
  | succ k ih =>
      rw [powCount]
      by_cases hn : n = k + 1
      · subst n
        rw [Finset.sum_eq_single (1, k)]
        · simp [Atom_count, ih]
        · rintro ⟨i, j⟩ hij hne
          rw [Finset.mem_antidiagonal] at hij
          by_cases hi : i = 1
          · have hj : j = k := by omega
            exact (hne (Prod.ext hi hj)).elim
          · simp [Atom_count, hi]
        · intro hmissing
          exfalso
          apply hmissing
          rw [Finset.mem_antidiagonal]
          omega
      · rw [Finset.sum_eq_zero]
        · simp [hn]
        · rintro ⟨i, j⟩ hij
          rw [Finset.mem_antidiagonal] at hij
          by_cases hi : i = 1
          · have hj : j ≠ k := by
              intro hj
              apply hn
              omega
            simp [Atom_count, hi, ih, hj]
          · simp [Atom_count, hi]

/-- `Atom^k` has one object at size `k`. -/
theorem powClass_Atom_count (k n : ℕ) :
    (powClass Atom k).count n = if n = k then 1 else 0 := by
  rw [powClass_count, powCount_Atom_count]

theorem powClass_Atom_three_count (n : ℕ) :
    (powClass Atom 3).count n = if n = 3 then 1 else 0 :=
  powClass_Atom_count 3 n

/-! ## A small composition-shaped example: `SEQ(Atom + Atom^2)` -/

/-- The positive class with one object of size 1 and one object of size 2. -/
noncomputable def AtomPlusAtomSq : CombinatorialClass :=
  Atom.disjSum (Atom.cartProd Atom)

/-- Its count sequence is `z + z^2`. -/
theorem AtomPlusAtomSq_count (n : ℕ) :
    AtomPlusAtomSq.count n = if n = 1 then 1 else if n = 2 then 1 else 0 := by
  rw [AtomPlusAtomSq, disjSum_transfer_count, Atom_count, cartProd_Atom_Atom_count]
  by_cases h1 : n = 1
  · simp [h1]
  · by_cases h2 : n = 2
    · simp [h1, h2]
    · simp [h1, h2]

theorem AtomPlusAtomSq_count_zero : AtomPlusAtomSq.count 0 = 0 := by
  rw [AtomPlusAtomSq_count]
  norm_num

/-- `(Atom + Atom^2)^2 = z^2 + 2z^3 + z^4`, verified at sizes 0 through 6. -/
example : (powClass AtomPlusAtomSq 2).count 0 = 0 := by
  rw [powClass_count]
  norm_num [powCount, AtomPlusAtomSq_count, Finset.antidiagonal]

example : (powClass AtomPlusAtomSq 2).count 1 = 0 := by
  rw [powClass_count]
  norm_num [powCount, AtomPlusAtomSq_count, Finset.antidiagonal]

example : (powClass AtomPlusAtomSq 2).count 2 = 1 := by
  rw [powClass_count]
  norm_num [powCount, AtomPlusAtomSq_count, Finset.antidiagonal]

example : (powClass AtomPlusAtomSq 2).count 3 = 2 := by
  rw [powClass_count]
  norm_num [powCount, AtomPlusAtomSq_count, Finset.antidiagonal]

example : (powClass AtomPlusAtomSq 2).count 4 = 1 := by
  rw [powClass_count]
  norm_num [powCount, AtomPlusAtomSq_count, Finset.antidiagonal]

example : (powClass AtomPlusAtomSq 2).count 5 = 0 := by
  rw [powClass_count]
  norm_num [powCount, AtomPlusAtomSq_count, Finset.antidiagonal]

example : (powClass AtomPlusAtomSq 2).count 6 = 0 := by
  rw [powClass_count]
  norm_num [powCount, AtomPlusAtomSq_count, Finset.antidiagonal]

/-- SEQ(Atom) has the geometric count sequence: one object at every size. -/
noncomputable def seqAtom : CombinatorialClass :=
  seqClass Atom Atom_count_zero

theorem seqAtom_count (n : ℕ) : seqAtom.count n = 1 := by
  induction n with
  | zero =>
      show (seqClass Atom Atom_count_zero).count 0 = 1
      rw [seqClass.count_zero]
  | succ n ih =>
      change (seqClass Atom Atom_count_zero).count n = 1 at ih
      show (seqClass Atom Atom_count_zero).count (n + 1) = 1
      rw [seqClass.count_succ]
      rw [Finset.sum_eq_single (1, n)]
      · rw [Atom_count]
        simp [ih]
      · rintro ⟨i, j⟩ hij hne
        rw [Finset.mem_antidiagonal] at hij
        by_cases hi : i = 1
        · have hj : j = n := by omega
          exact (hne (Prod.ext hi hj)).elim
        · simp [Atom_count, hi]
      · intro hmissing
        exfalso
        apply hmissing
        rw [Finset.mem_antidiagonal]
        omega

/-- SEQ(Atom + Atom^2), the ordinary composition `1/(1 - z - z^2)`. -/
noncomputable def seqAtomPlusAtomSq : CombinatorialClass :=
  seqClass AtomPlusAtomSq AtomPlusAtomSq_count_zero

theorem seqAtomPlusAtomSq_count_zero : seqAtomPlusAtomSq.count 0 = 1 := by
  show (seqClass AtomPlusAtomSq AtomPlusAtomSq_count_zero).count 0 = 1
  rw [seqClass.count_zero]

theorem seqAtomPlusAtomSq_count_one : seqAtomPlusAtomSq.count 1 = 1 := by
  show (seqClass AtomPlusAtomSq AtomPlusAtomSq_count_zero).count (0 + 1) = 1
  rw [seqClass.count_succ]
  norm_num [Finset.antidiagonal, AtomPlusAtomSq_count]
  change seqAtomPlusAtomSq.count 0 = 1
  exact seqAtomPlusAtomSq_count_zero

theorem seqAtomPlusAtomSq_count_two : seqAtomPlusAtomSq.count 2 = 2 := by
  show (seqClass AtomPlusAtomSq AtomPlusAtomSq_count_zero).count (1 + 1) = 2
  rw [seqClass.count_succ]
  norm_num [Finset.antidiagonal, AtomPlusAtomSq_count]
  change seqAtomPlusAtomSq.count 1 + seqAtomPlusAtomSq.count 0 = 2
  rw [seqAtomPlusAtomSq_count_one, seqAtomPlusAtomSq_count_zero]

theorem seqAtomPlusAtomSq_count_three : seqAtomPlusAtomSq.count 3 = 3 := by
  show (seqClass AtomPlusAtomSq AtomPlusAtomSq_count_zero).count (2 + 1) = 3
  rw [seqClass.count_succ]
  norm_num [Finset.antidiagonal, AtomPlusAtomSq_count]
  change seqAtomPlusAtomSq.count 2 + seqAtomPlusAtomSq.count 1 = 3
  rw [seqAtomPlusAtomSq_count_two, seqAtomPlusAtomSq_count_one]

theorem seqAtomPlusAtomSq_count_four : seqAtomPlusAtomSq.count 4 = 5 := by
  show (seqClass AtomPlusAtomSq AtomPlusAtomSq_count_zero).count (3 + 1) = 5
  rw [seqClass.count_succ]
  norm_num [Finset.antidiagonal, AtomPlusAtomSq_count]
  change seqAtomPlusAtomSq.count 3 + seqAtomPlusAtomSq.count 2 = 5
  rw [seqAtomPlusAtomSq_count_three, seqAtomPlusAtomSq_count_two]

theorem seqAtomPlusAtomSq_count_five : seqAtomPlusAtomSq.count 5 = 8 := by
  show (seqClass AtomPlusAtomSq AtomPlusAtomSq_count_zero).count (4 + 1) = 8
  rw [seqClass.count_succ]
  norm_num [Finset.antidiagonal, AtomPlusAtomSq_count]
  change seqAtomPlusAtomSq.count 4 + seqAtomPlusAtomSq.count 3 = 8
  rw [seqAtomPlusAtomSq_count_four, seqAtomPlusAtomSq_count_three]

theorem seqAtomPlusAtomSq_count_six : seqAtomPlusAtomSq.count 6 = 13 := by
  show (seqClass AtomPlusAtomSq AtomPlusAtomSq_count_zero).count (5 + 1) = 13
  rw [seqClass.count_succ]
  norm_num [Finset.antidiagonal, AtomPlusAtomSq_count]
  change seqAtomPlusAtomSq.count 5 + seqAtomPlusAtomSq.count 4 = 13
  rw [seqAtomPlusAtomSq_count_five, seqAtomPlusAtomSq_count_four]

/-- The first seven counts of `SEQ(Atom + Atom^2)` are Fibonacci numbers. -/
example :
    [seqAtomPlusAtomSq.count 0, seqAtomPlusAtomSq.count 1, seqAtomPlusAtomSq.count 2,
      seqAtomPlusAtomSq.count 3, seqAtomPlusAtomSq.count 4, seqAtomPlusAtomSq.count 5,
      seqAtomPlusAtomSq.count 6] = [1, 1, 2, 3, 5, 8, 13] := by
  rw [seqAtomPlusAtomSq_count_zero, seqAtomPlusAtomSq_count_one,
    seqAtomPlusAtomSq_count_two, seqAtomPlusAtomSq_count_three, seqAtomPlusAtomSq_count_four,
    seqAtomPlusAtomSq_count_five, seqAtomPlusAtomSq_count_six]

end CombinatorialClass
