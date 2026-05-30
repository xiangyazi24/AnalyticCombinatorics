import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Fintype.Card

/-!
# Ch1 §I.1 — Combinatorial classes and ordinary generating functions

A faithful encoding of Flajolet & Sedgewick, *Analytic Combinatorics*, Part A,
Chapter I, §I.1. A combinatorial class is a set of objects equipped with a size
function such that only finitely many objects have any given size. We encode it
as a graded family of finite types `Obj : ℕ → Type`, where `Obj n` is the set of
objects of size `n`. Its counting sequence is `Aₙ = #(Obj n)`, and its *ordinary
generating function* (OGF) is `A(z) = ∑ₙ Aₙ zⁿ`, here a formal power series over
`ℚ`.

This file defines the OGF, the `CombClass` structure, and the three primitive
classes (empty `∅`, neutral `ε`, atom `Z`) with their counting sequences and
generating functions `ε(z) = 1`, `Z(z) = z`. The admissible constructions (sum,
product, sequence) and their transfer theorems live in sibling files.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries

/-- The ordinary generating function of a counting sequence `a : ℕ → ℕ`, as a
formal power series over `ℚ` (F&S §I.1: `A(z) = ∑ₙ aₙ zⁿ`). The class-level
OGF `CombClass.ogf` is defined on top of this. -/
noncomputable def ogfSeq (a : ℕ → ℕ) : ℚ⟦X⟧ := mk fun n => (a n : ℚ)

@[simp] lemma coeff_ogfSeq (a : ℕ → ℕ) (n : ℕ) : coeff n (ogfSeq a) = (a n : ℚ) := by
  rw [ogfSeq, coeff_mk]

/-- A combinatorial class (F&S §I.1): a graded family of finite types, with
`Obj n` the objects of size `n`. The `Fintype` field records that each size
class is finite, which is exactly F&S's standing finiteness condition. -/
structure CombClass where
  /-- Objects of size `n`. -/
  Obj : ℕ → Type
  /-- Each size class is finite. -/
  finObj : ∀ n, Fintype (Obj n)

attribute [instance] CombClass.finObj

/-- The counting sequence `Aₙ = #{objects of size n}`. -/
def CombClass.counts (C : CombClass) (n : ℕ) : ℕ := Fintype.card (C.Obj n)

/-- The ordinary generating function of a combinatorial class. -/
noncomputable def CombClass.ogf (C : CombClass) : ℚ⟦X⟧ := ogfSeq C.counts

lemma CombClass.ogf_eq (C : CombClass) : C.ogf = ogfSeq C.counts := rfl

@[simp] lemma CombClass.coeff_ogf (C : CombClass) (n : ℕ) :
    coeff n C.ogf = (C.counts n : ℚ) := by
  rw [CombClass.ogf, coeff_ogfSeq]

/-! ### Primitive classes

We encode the primitive classes with `Obj n := Fin (· n)` so that the `Fintype`
instance is uniform; their entire content is their counting sequence. -/

/-- The empty class `∅`: no objects of any size. -/
def CombClass.empty : CombClass where
  Obj _ := Fin 0
  finObj _ := inferInstance

/-- The neutral class `ε`: a single object of size `0`. -/
def CombClass.neutral : CombClass where
  Obj n := Fin (if n = 0 then 1 else 0)
  finObj _ := inferInstance

/-- The atomic class `Z`: a single object of size `1`. -/
def CombClass.atom : CombClass where
  Obj n := Fin (if n = 1 then 1 else 0)
  finObj _ := inferInstance

@[simp] lemma CombClass.counts_empty (n : ℕ) : CombClass.empty.counts n = 0 :=
  Fintype.card_fin _

@[simp] lemma CombClass.counts_neutral (n : ℕ) :
    CombClass.neutral.counts n = if n = 0 then 1 else 0 :=
  Fintype.card_fin _

@[simp] lemma CombClass.counts_atom (n : ℕ) :
    CombClass.atom.counts n = if n = 1 then 1 else 0 :=
  Fintype.card_fin _

/-- `∅(z) = 0`. -/
lemma CombClass.ogf_empty : CombClass.empty.ogf = 0 := by
  ext n; simp

/-- `ε(z) = 1`. -/
lemma CombClass.ogf_neutral : CombClass.neutral.ogf = 1 := by
  ext n
  simp only [CombClass.coeff_ogf, CombClass.counts_neutral, coeff_one]
  by_cases h : n = 0 <;> simp [h]

/-- `Z(z) = z`. -/
lemma CombClass.ogf_atom : CombClass.atom.ogf = X := by
  ext n
  simp only [CombClass.coeff_ogf, CombClass.counts_atom, coeff_X]
  by_cases h : n = 1 <;> simp [h]

end AnalyticCombinatorics.Ch1
