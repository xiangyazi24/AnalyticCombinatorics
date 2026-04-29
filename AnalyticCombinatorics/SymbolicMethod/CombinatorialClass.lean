/-
  Analytic Combinatorics — Symbolic Method
  Chapter I: Combinatorial Classes and Ordinary Generating Functions

  A combinatorial class is a set A equipped with a size function |·| : A → ℕ
  such that for each n, the set Aₙ = {a ∈ A | |a| = n} is finite.
  The ordinary generating function is A(z) = Σₙ aₙ zⁿ where aₙ = #Aₙ.

  Reference: Flajolet & Sedgewick, Analytic Combinatorics, Chapter I.
-/
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Finset.Card

open PowerSeries

/-- A combinatorial class: a type with a size function and finite level sets. -/
structure CombinatorialClass where
  /-- The underlying type of objects. -/
  Obj : Type*
  /-- Size function assigning a natural number to each object. -/
  size : Obj → ℕ
  /-- Each level set (objects of a given size) is finite. -/
  finite_level : ∀ n : ℕ, Set.Finite {a : Obj | size a = n}

namespace CombinatorialClass

variable (A : CombinatorialClass)

/-- The n-th level set of a combinatorial class. -/
noncomputable def level (n : ℕ) : Finset A.Obj :=
  (A.finite_level n).toFinset

/-- The counting sequence: number of objects of size n. -/
noncomputable def count (n : ℕ) : ℕ := (A.level n).card

/-- The ordinary generating function A(z) = Σ aₙ zⁿ. -/
noncomputable def ogf : PowerSeries ℕ :=
  fun s => A.count (s ())

/-- The coefficient of zⁿ in the OGF equals the count. -/
@[simp]
theorem coeff_ogf (n : ℕ) : coeff n A.ogf = A.count n := by
  sorry

end CombinatorialClass

/-
  The neutral combinatorial classes:
  - ε (epsilon): one object of size 0
  - Z: one object of size 1 (the atom)
-/

/-- The epsilon class: a single object of size 0. -/
def Epsilon : CombinatorialClass where
  Obj := Unit
  size _ := 0
  finite_level _ := Set.finite_univ.subset (Set.subset_univ _)

/-- The atom class Z: a single object of size 1. -/
def Atom : CombinatorialClass where
  Obj := Unit
  size _ := 1
  finite_level _ := Set.finite_univ.subset (Set.subset_univ _)
