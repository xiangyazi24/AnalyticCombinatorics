/-
  Analytic Combinatorics — Examples
  Binary strings with no two consecutive ones

  F&S Example I.4: binary strings of length n with no adjacent true bits
  are counted by F_{n+2}.
-/
import Mathlib.Data.Fintype.Vector
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass

open CombinatorialClass

/-- No two adjacent entries of a Boolean list are both `true`. -/
def noTwoOnes : List Bool → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => ¬ (a = true ∧ b = true) ∧ noTwoOnes (b :: rest)

instance instDecidableNoTwoOnes (l : List Bool) : Decidable (noTwoOnes l) := by
  induction l with
  | nil => exact isTrue trivial
  | cons a t ih =>
      cases t with
      | nil => exact isTrue trivial
      | cons b rest =>
          dsimp [noTwoOnes]
          haveI := ih
          infer_instance

/-- Length-n binary strings with no adjacent `true`s. -/
abbrev NoConsecOnesWord (n : ℕ) :=
  { w : List.Vector Bool n // noTwoOnes w.val }

/-- Binary strings whose size is their length, restricted to no adjacent ones. -/
def noConsecOnesClass : CombinatorialClass where
  Obj := Σ n : ℕ, NoConsecOnesWord n
  size := Sigma.fst
  finite_level n := by
    have hfin : Set.Finite (Set.univ : Set (NoConsecOnesWord n)) := Set.toFinite _
    apply Set.Finite.subset (hfin.image (Sigma.mk n))
    rintro ⟨k, w⟩ hw
    simp only [Set.mem_setOf_eq] at hw
    change k = n at hw
    subst k
    exact ⟨w, Set.mem_univ _, rfl⟩

namespace noConsecOnesClass

/-- At level `n`, the class is exactly the finite type of length-n restricted words. -/
theorem count_eq_card (n : ℕ) :
    noConsecOnesClass.count n = Fintype.card (NoConsecOnesWord n) := by
  rw [CombinatorialClass.count]
  have hcard : (noConsecOnesClass.level n).card =
      (Finset.univ : Finset (NoConsecOnesWord n)).card := by
    refine Finset.card_bij'
      (s := noConsecOnesClass.level n)
      (t := (Finset.univ : Finset (NoConsecOnesWord n)))
      (fun x hx => by
        obtain ⟨k, w⟩ := x
        have hsize : noConsecOnesClass.size ⟨k, w⟩ = n :=
          (CombinatorialClass.level_mem_iff (C := noConsecOnesClass) ⟨k, w⟩).mp hx
        change k = n at hsize
        subst k
        exact w)
      (fun w _ => (⟨n, w⟩ : noConsecOnesClass.Obj))
      ?_ ?_ ?_ ?_
    · intro _ _
      exact Finset.mem_univ _
    · intro w _
      exact (CombinatorialClass.level_mem_iff (C := noConsecOnesClass) ⟨n, w⟩).mpr rfl
    · intro x hx
      obtain ⟨k, w⟩ := x
      have hsize : noConsecOnesClass.size ⟨k, w⟩ = n :=
        (CombinatorialClass.level_mem_iff (C := noConsecOnesClass) ⟨k, w⟩).mp hx
      change k = n at hsize
      subst k
      rfl
    · intro w _
      rfl
  rw [hcard, Finset.card_univ]

end noConsecOnesClass

-- TODO: prove `noConsecOnesClass.count n = Nat.fib (n + 2)`.

/-! Sanity checks: 1, 2, 3, 5, 8, 13, 21 for n = 0..6. -/
example : noConsecOnesClass.count 0 = 1 := by
  rw [noConsecOnesClass.count_eq_card]
  decide

example : noConsecOnesClass.count 1 = 2 := by
  rw [noConsecOnesClass.count_eq_card]
  decide

example : noConsecOnesClass.count 2 = 3 := by
  rw [noConsecOnesClass.count_eq_card]
  decide

example : noConsecOnesClass.count 3 = 5 := by
  rw [noConsecOnesClass.count_eq_card]
  decide

example : noConsecOnesClass.count 4 = 8 := by
  rw [noConsecOnesClass.count_eq_card]
  decide

example : noConsecOnesClass.count 5 = 13 := by
  rw [noConsecOnesClass.count_eq_card]
  decide

example : noConsecOnesClass.count 6 = 21 := by
  rw [noConsecOnesClass.count_eq_card]
  decide
