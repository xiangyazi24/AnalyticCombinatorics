/-
  Chapter I § I.2 — Cycles (CYC construction)

  This file records the clean Atom case of F&S Proposition I.2.  A full
  unlabelled CYC(B) construction as rotation orbits requires a quotient/Burnside
  development.  Here `cycClass` is the direct-count realization used once the
  cycle counts are known, and `cycAtomClass` instantiates it with the usual
  count of circular permutations.
-/
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Totient
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass
import AnalyticCombinatorics.PartA.Ch1.Sequences
import AnalyticCombinatorics.PartA.Ch2.LabelledClass

set_option linter.style.show false

open PowerSeries CombinatorialClass

namespace CombinatorialClass

/-- Direct-count realization of a cycle construction.

Instead of constructing rotation orbits of nonempty lists, this packages an
already established counting sequence as a combinatorial class. -/
noncomputable def cycClass (cycleCount : ℕ → ℕ) : CombinatorialClass where
  Obj := Σ n : ℕ, Fin (cycleCount n)
  size x := x.1
  finite_level n := by
    refine Set.Finite.subset
      ((Set.finite_univ.image
        fun i : Fin (cycleCount n) => (⟨n, i⟩ : Σ m : ℕ, Fin (cycleCount m)))) ?_
    rintro ⟨m, i⟩ h
    change m = n at h
    subst m
    exact Set.mem_image_of_mem
      (fun i : Fin (cycleCount n) => (⟨n, i⟩ : Σ m : ℕ, Fin (cycleCount m)))
      (Set.mem_univ i)

/-- The count of circular permutations on `n` labelled atoms:
zero at size zero, and `(n - 1)!` at positive sizes. -/
def cycAtomCount (n : ℕ) : ℕ :=
  if n = 0 then 0 else (n - 1).factorial

/-- The direct-count class for cycles of atoms. -/
noncomputable def cycAtomClass : CombinatorialClass :=
  cycClass cycAtomCount

/-- `cycClass` has the prescribed counting sequence. -/
theorem cycClass_count (cycleCount : ℕ → ℕ) (n : ℕ) :
    (cycClass cycleCount).count n = cycleCount n := by
  simp only [count]
  calc
    ((cycClass cycleCount).level n).card =
        (Finset.univ : Finset (Fin (cycleCount n))).card := by
      symm
      refine Finset.card_bij
        (fun i _ => (⟨n, i⟩ : (cycClass cycleCount).Obj)) ?_ ?_ ?_
      · intro i _
        exact (level_mem_iff (C := cycClass cycleCount) (n := n) ⟨n, i⟩).mpr rfl
      · intro i _ j _ hij
        cases hij
        rfl
      · intro x hx
        obtain ⟨m, i⟩ := x
        have hm : m = n :=
          (level_mem_iff (C := cycClass cycleCount) (n := n) ⟨m, i⟩).mp hx
        subst m
        exact ⟨i, Finset.mem_univ i, rfl⟩
    _ = cycleCount n := by simp

@[simp]
theorem cycAtomClass_count (n : ℕ) :
    cycAtomClass.count n = cycAtomCount n := by
  rw [cycAtomClass, cycClass_count]

@[simp]
theorem cycAtomCount_zero : cycAtomCount 0 = 0 := by
  simp [cycAtomCount]

@[simp]
theorem cycAtomCount_succ (n : ℕ) :
    cycAtomCount (n + 1) = n.factorial := by
  simp [cycAtomCount]

/-- Coefficient/count form of the Atom-cycle formula:
positive sizes have `(n - 1)!` cycles. -/
theorem cycAtom_ogf_coeff (n : ℕ) (hn : 0 < n) :
    (cycAtomCount n : ℚ) = (n - 1).factorial := by
  simp [cycAtomCount, Nat.ne_of_gt hn]

/-- The EGF coefficient of Atom-cycles is `1 / n` at positive sizes,
the coefficient sequence of `-log(1 - z)`. -/
theorem cycAtom_egf_coeff (n : ℕ) (hn : 0 < n) :
    (cycAtomCount n : ℚ) / n.factorial = 1 / (n : ℚ) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [cycAtomCount_succ, Nat.factorial_succ]
  norm_num only [Nat.cast_mul, Nat.cast_succ, Nat.cast_one]
  field_simp [show ((m : ℚ) + 1) ≠ 0 by positivity,
    show (m.factorial : ℚ) ≠ 0 by positivity]

/-- Cycles of atoms agree with the existing labelled CYC count at every size. -/
theorem cycAtomCount_eq_labelCycCount (n : ℕ) :
    (cycAtomCount n : ℚ) = labelCycCount Atom n := by
  cases n with
  | zero =>
      simp [cycAtomCount, labelCycCount]
  | succ n =>
      rw [cycAtomCount_succ, labelCycCount_Atom_succ]

example : cycAtomCount 1 = 1 := by
  simp

example : cycAtomCount 2 = 1 := by
  simp

example : cycAtomCount 3 = 2 := by
  simp

example : cycAtomCount 4 = 6 := by
  decide

example : cycAtomCount 5 = 24 := by
  decide

example : cycAtomClass.count 1 = 1 := by
  simp

example : cycAtomClass.count 2 = 1 := by
  simp

example : cycAtomClass.count 3 = 2 := by
  simp

example : cycAtomClass.count 4 = 6 := by
  rw [cycAtomClass_count, cycAtomCount_succ]
  decide

example : cycAtomClass.count 5 = 24 := by
  rw [cycAtomClass_count, cycAtomCount_succ]
  decide

end CombinatorialClass
