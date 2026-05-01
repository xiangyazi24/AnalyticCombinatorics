import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass
import Mathlib.Combinatorics.Derangements.Basic
import Mathlib.Combinatorics.Derangements.Finite
import Mathlib.Data.Fintype.Perm

open CombinatorialClass

namespace Nat

/-- Namespace bridge for Mathlib's derangement-counting sequence. -/
abbrev numDerangements : ℕ → ℕ := _root_.numDerangements

end Nat

/-- A derangement of size `n` is a fixed-point-free permutation of `Fin n`. -/
def derangementClass : CombinatorialClass where
  Obj := Σ n : ℕ, { σ : Equiv.Perm (Fin n) // ∀ i, σ i ≠ i }
  size := Sigma.fst
  finite_level n := by
    have hfin : Set.Finite (Set.univ :
      Set { σ : Equiv.Perm (Fin n) // ∀ i, σ i ≠ i }) := Set.toFinite _
    apply Set.Finite.subset (hfin.image (Sigma.mk n))
    rintro ⟨k, σ⟩ hkσ
    simp only [Set.mem_setOf_eq] at hkσ
    change k = n at hkσ
    subst k
    exact ⟨σ, Set.mem_univ _, rfl⟩

namespace derangementClass

/-- Count of derangements of size `n` equals Mathlib's `Nat.numDerangements`. -/
theorem count_eq_numDerangements (n : ℕ) :
    derangementClass.count n = Nat.numDerangements n := by
  rw [CombinatorialClass.count]
  have hcard : (derangementClass.level n).card =
      (Finset.univ : Finset { σ : Equiv.Perm (Fin n) // ∀ i, σ i ≠ i }).card := by
    refine Finset.card_bij'
      (s := derangementClass.level n)
      (t := (Finset.univ : Finset { σ : Equiv.Perm (Fin n) // ∀ i, σ i ≠ i }))
      (fun x hx => by
        obtain ⟨k, σ⟩ := x
        have hsize : derangementClass.size ⟨k, σ⟩ = n :=
          (CombinatorialClass.level_mem_iff (C := derangementClass) ⟨k, σ⟩).mp hx
        change k = n at hsize
        subst k
        exact σ)
      (fun σ _ => (⟨n, σ⟩ : derangementClass.Obj))
      ?_ ?_ ?_ ?_
    · intro _ _
      exact Finset.mem_univ _
    · intro σ _
      exact (CombinatorialClass.level_mem_iff (C := derangementClass) ⟨n, σ⟩).mpr rfl
    · intro x hx
      obtain ⟨k, σ⟩ := x
      have hsize : derangementClass.size ⟨k, σ⟩ = n :=
        (CombinatorialClass.level_mem_iff (C := derangementClass) ⟨k, σ⟩).mp hx
      change k = n at hsize
      subst k
      rfl
    · intro σ _
      rfl
  rw [hcard, Finset.card_univ]
  have htype :
      Fintype.card { σ : Equiv.Perm (Fin n) // ∀ i, σ i ≠ i } =
        Fintype.card (derangements (Fin n)) := by
    exact Fintype.card_congr
      { toFun := fun σ => ⟨σ.1, by
          show σ.1 ∈ derangements (Fin n)
          rw [derangements]
          exact σ.2⟩
        invFun := fun σ => ⟨σ.1, show ∀ i, σ.1 i ≠ i from σ.2⟩
        left_inv := by
          intro σ
          cases σ
          rfl
        right_inv := by
          intro σ
          cases σ
          rfl }
  rw [htype]
  exact card_derangements_fin_eq_numDerangements

end derangementClass

/-- Count of derangements of size `n` equals Mathlib's `Nat.numDerangements`. -/
theorem derangementClass_count_eq_numDerangements (n : ℕ) :
    derangementClass.count n = Nat.numDerangements n :=
  derangementClass.count_eq_numDerangements n

example : derangementClass.count 0 = 1 := by
  rw [derangementClass_count_eq_numDerangements]
  decide

example : derangementClass.count 1 = 0 := by
  rw [derangementClass_count_eq_numDerangements]
  decide

example : derangementClass.count 2 = 1 := by
  rw [derangementClass_count_eq_numDerangements]
  decide

example : derangementClass.count 3 = 2 := by
  rw [derangementClass_count_eq_numDerangements]
  decide

example : derangementClass.count 4 = 9 := by
  rw [derangementClass_count_eq_numDerangements]
  decide

example : derangementClass.count 5 = 44 := by
  rw [derangementClass_count_eq_numDerangements]
  decide

example : derangementClass.count 6 = 265 := by
  rw [derangementClass_count_eq_numDerangements]
  decide
