/-
  Analytic Combinatorics — Part A: Symbolic Method
  Chapter I: Combinatorial Structures and Ordinary Generating Functions

  § I.1  Symbolic enumeration methods
  § I.2  Admissible constructions and transfer lemmas
  § I.3  Trees, integers, strings, and their OGFs

  Reference: F&S Chapter I.
-/
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Finset.Card

open PowerSeries

/-! ## I.1 Combinatorial classes -/

/-- A combinatorial class: objects with a size function and finite level sets. -/
structure CombinatorialClass where
  Obj   : Type*
  size  : Obj → ℕ
  finite_level : ∀ n : ℕ, Set.Finite {a : Obj | size a = n}

namespace CombinatorialClass

variable (A B : CombinatorialClass)

/-- Objects of size n. -/
noncomputable def level (n : ℕ) : Finset A.Obj :=
  (A.finite_level n).toFinset

/-- Counting sequence: aₙ = #{a ∈ A | |a| = n}. -/
noncomputable def count (n : ℕ) : ℕ := (A.level n).card

/-- OGF: A(z) = Σₙ aₙ zⁿ ∈ ℕ[[z]]. -/
noncomputable def ogf : PowerSeries ℕ := fun s => A.count (s ())

theorem coeff_ogf (n : ℕ) : coeff n A.ogf = A.count n := by
  sorry

/-! ## I.2 Neutral classes -/

/-- ε: one object of size 0. OGF = 1. -/
def Epsilon : CombinatorialClass where
  Obj := Unit
  size _ := 0
  finite_level _ := Set.finite_univ.subset (Set.subset_univ _)

/-- Z: one object of size 1 (the atom). OGF = z. -/
def Atom : CombinatorialClass where
  Obj := Unit
  size _ := 1
  finite_level _ := Set.finite_univ.subset (Set.subset_univ _)

theorem Epsilon_ogf : Epsilon.ogf = 1 := by sorry
theorem Atom_ogf : Atom.ogf = PowerSeries.X := by sorry

/-! ## I.2 Admissible constructions -/

/-- Disjoint union A + B. OGF satisfies (A+B)(z) = A(z) + B(z). -/
noncomputable def disjSum : CombinatorialClass where
  Obj := A.Obj ⊕ B.Obj
  size := Sum.elim A.size B.size
  finite_level n := by
    apply Set.Finite.subset ((A.finite_level n).image Sum.inl |>.union
                              ((B.finite_level n).image Sum.inr))
    rintro (a | b) hx <;> simp [Sum.elim] at hx
    · exact Set.mem_union_left _ (Set.mem_image_of_mem _ hx)
    · exact Set.mem_union_right _ (Set.mem_image_of_mem _ hx)

/-- OGF of disjoint union = sum of OGFs. -/
theorem disjSum_ogf : (A.disjSum B).ogf = A.ogf + B.ogf := by sorry

/-- Cartesian product A × B. Size |(a,b)| = |a| + |b|. OGF = A(z)·B(z). -/
noncomputable def cartProd : CombinatorialClass where
  Obj := A.Obj × B.Obj
  size := fun ⟨a, b⟩ => A.size a + B.size b
  finite_level n := by
    apply Set.Finite.subset
      (Set.finite_iUnion (fun k : Fin (n + 1) =>
        (A.finite_level k.val).prod (B.finite_level (n - k.val))))
    rintro ⟨a, b⟩ hx
    simp only [Set.mem_setOf_eq] at hx
    simp only [Set.mem_iUnion, Set.mem_prod, Set.mem_setOf_eq]
    sorry

/-- OGF of Cartesian product = product of OGFs. -/
theorem cartProd_ogf : (A.cartProd B).ogf = A.ogf * B.ogf := by sorry

end CombinatorialClass
