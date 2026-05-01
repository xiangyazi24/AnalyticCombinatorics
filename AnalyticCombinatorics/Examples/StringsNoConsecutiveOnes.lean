/-
  Analytic Combinatorics — Examples
  Binary strings with no two consecutive ones

  F&S Example I.4: binary strings of length n with no adjacent true bits
  are counted by F_{n+2}.
-/
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Vector.Basic
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass

open CombinatorialClass
open List.Vector

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

private lemma noTwoOnes_tail_list {l : List Bool} (h : noTwoOnes l) :
    noTwoOnes l.tail := by
  cases l with
  | nil => trivial
  | cons a t =>
      cases t with
      | nil => trivial
      | cons b rest => exact h.2

private lemma noTwoOnes_vector_tail {n : ℕ} (v : List.Vector Bool (n + 1))
    (h : noTwoOnes v.val) : noTwoOnes v.tail.val := by
  simpa [List.Vector.tail_val] using noTwoOnes_tail_list h

private lemma noTwoOnes_false_cons {l : List Bool} (h : noTwoOnes l) :
    noTwoOnes (false :: l) := by
  cases l with
  | nil => trivial
  | cons b rest =>
      simp [noTwoOnes, h]

private lemma noTwoOnes_true_false_cons {l : List Bool} (h : noTwoOnes l) :
    noTwoOnes (true :: false :: l) := by
  exact ⟨by simp, noTwoOnes_false_cons h⟩

/-- Split a valid word of length `n + 2` by its first bit. -/
private def noConsecOnesWord_splitEquiv (n : ℕ) :
    NoConsecOnesWord (n + 2) ≃ NoConsecOnesWord (n + 1) ⊕ NoConsecOnesWord n where
  toFun w :=
    if h : w.1.head = false then
      Sum.inl ⟨w.1.tail, noTwoOnes_vector_tail w.1 w.2⟩
    else
      Sum.inr ⟨w.1.tail.tail,
        noTwoOnes_vector_tail w.1.tail (noTwoOnes_vector_tail w.1 w.2)⟩
  invFun
    | Sum.inl w =>
        ⟨false ::ᵥ w.1, by
          simpa [List.Vector.cons_val] using noTwoOnes_false_cons w.2⟩
    | Sum.inr w =>
        ⟨true ::ᵥ false ::ᵥ w.1, by
          simpa [List.Vector.cons_val] using noTwoOnes_true_false_cons w.2⟩
  left_inv := by
    intro w
    cases w with
    | mk v hv =>
        obtain ⟨a, t, rfl⟩ := List.Vector.exists_eq_cons v
        obtain ⟨b, r, rfl⟩ := List.Vector.exists_eq_cons t
        cases a <;> cases b <;> simp [noTwoOnes] at hv ⊢
  right_inv := by
    intro w
    cases w with
    | inl w =>
        cases w with
        | mk val h =>
            simp
    | inr w =>
        cases w with
        | mk val h =>
            simp

private lemma noConsecOnesClass_count_zero :
    noConsecOnesClass.count 0 = 1 := by
  rw [noConsecOnesClass.count_eq_card]
  decide

private lemma noConsecOnesClass_count_one :
    noConsecOnesClass.count 1 = 2 := by
  rw [noConsecOnesClass.count_eq_card]
  decide

private lemma noConsecOnesClass_count_succ_succ (n : ℕ) :
    noConsecOnesClass.count (n + 2) =
      noConsecOnesClass.count (n + 1) + noConsecOnesClass.count n := by
  rw [noConsecOnesClass.count_eq_card, noConsecOnesClass.count_eq_card,
    noConsecOnesClass.count_eq_card]
  calc
    Fintype.card (NoConsecOnesWord (n + 2))
        = Fintype.card (NoConsecOnesWord (n + 1) ⊕ NoConsecOnesWord n) := by
          exact Fintype.card_congr (noConsecOnesWord_splitEquiv n)
    _ = Fintype.card (NoConsecOnesWord (n + 1)) +
        Fintype.card (NoConsecOnesWord n) := by
          rw [Fintype.card_sum]

/-- Binary strings of length `n` with no two consecutive ones are counted by `fib (n + 2)`. -/
theorem noConsecOnesClass_count_eq_fib (n : ℕ) :
    noConsecOnesClass.count n = Nat.fib (n + 2) := by
  induction n using Nat.twoStepInduction with
  | zero =>
      rw [noConsecOnesClass_count_zero, Nat.fib_two]
  | one =>
      rw [noConsecOnesClass_count_one]
      decide
  | more n ih0 ih1 =>
      rw [noConsecOnesClass_count_succ_succ, ih0, ih1]
      rw [show n + 1 + 2 = (n + 1) + 2 by omega]
      rw [show n + 2 + 2 = (n + 2) + 2 by omega]
      rw [show (n + 1) + 2 = (n + 2) + 1 by omega]
      rw [show Nat.fib ((n + 2) + 1) + Nat.fib (n + 2) =
        Nat.fib (n + 2) + Nat.fib ((n + 2) + 1) by ac_rfl]
      exact (Nat.fib_add_two (n := n + 2)).symm

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

/-! Sanity checks from the closed form for n = 7..18. -/
example : noConsecOnesClass.count 7 = 34 := by
  rw [noConsecOnesClass_count_eq_fib]
  decide

example : noConsecOnesClass.count 8 = 55 := by
  rw [noConsecOnesClass_count_eq_fib]
  decide

example : noConsecOnesClass.count 9 = 89 := by
  rw [noConsecOnesClass_count_eq_fib]
  decide

example : noConsecOnesClass.count 10 = 144 := by
  rw [noConsecOnesClass_count_eq_fib]
  decide

example : noConsecOnesClass.count 11 = 233 := by
  rw [noConsecOnesClass_count_eq_fib]
  decide

example : noConsecOnesClass.count 12 = 377 := by
  rw [noConsecOnesClass_count_eq_fib]
  decide

example : noConsecOnesClass.count 13 = 610 := by
  rw [noConsecOnesClass_count_eq_fib]
  decide

example : noConsecOnesClass.count 14 = 987 := by
  rw [noConsecOnesClass_count_eq_fib]
  decide

example : noConsecOnesClass.count 15 = 1597 := by
  rw [noConsecOnesClass_count_eq_fib]
  decide

example : noConsecOnesClass.count 16 = 2584 := by
  rw [noConsecOnesClass_count_eq_fib]
  decide

example : noConsecOnesClass.count 17 = 4181 := by
  rw [noConsecOnesClass_count_eq_fib]
  decide

example : noConsecOnesClass.count 18 = 6765 := by
  rw [noConsecOnesClass_count_eq_fib]
  decide

example : noConsecOnesClass.count 19 = 10946 := by
  rw [noConsecOnesClass_count_eq_fib]
  decide

example : noConsecOnesClass.count 20 = 17711 := by
  rw [noConsecOnesClass_count_eq_fib]
  decide

example : noConsecOnesClass.count 21 = 28657 := by
  rw [noConsecOnesClass_count_eq_fib]
  decide
