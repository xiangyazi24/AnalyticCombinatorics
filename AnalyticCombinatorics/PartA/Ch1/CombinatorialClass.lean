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
import Mathlib.Data.Finset.Sum

open PowerSeries

/-! ## I.1 Combinatorial classes -/

/-- A combinatorial class: objects with a size function and finite level sets. -/
structure CombinatorialClass where
  Obj : Type*
  size : Obj → ℕ
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
  show A.count ((Finsupp.single () n) ()) = A.count n
  simp [Finsupp.single_eq_same]

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

private lemma level_mem_iff {C : CombinatorialClass} {n : ℕ} (x : C.Obj) :
    x ∈ C.level n ↔ C.size x = n := by
  simp [level, Set.Finite.mem_toFinset]

theorem Epsilon_ogf : Epsilon.ogf = 1 := by
  ext n
  rw [coeff_ogf, coeff_one]
  simp only [count]
  haveI : Unique Epsilon.Obj := inferInstanceAs (Unique Unit)
  have hmem : ∀ x : Epsilon.Obj, x ∈ Epsilon.level n ↔ n = 0 := fun x => by
    rw [level_mem_iff]; show (0 : ℕ) = n ↔ n = 0; omega
  by_cases h : n = 0
  · have hcard : (Epsilon.level n).card = 1 := by
      rw [Finset.card_eq_one]
      exact ⟨(), Finset.eq_singleton_iff_unique_mem.mpr
        ⟨(hmem ()).mpr h, fun x _ => Unique.eq_default x⟩⟩
    rw [hcard]; simp [h]
  · have hcard : (Epsilon.level n).card = 0 := by
      rw [Finset.card_eq_zero]
      exact Finset.eq_empty_of_forall_notMem (fun x hx => h ((hmem x).mp hx))
    rw [hcard]; simp [h]

theorem Atom_ogf : Atom.ogf = PowerSeries.X := by
  ext n
  rw [coeff_ogf, coeff_X]
  simp only [count]
  haveI : Unique Atom.Obj := inferInstanceAs (Unique Unit)
  have hmem : ∀ x : Atom.Obj, x ∈ Atom.level n ↔ n = 1 := fun x => by
    rw [level_mem_iff]; show (1 : ℕ) = n ↔ n = 1; omega
  by_cases h : n = 1
  · have hcard : (Atom.level n).card = 1 := by
      rw [Finset.card_eq_one]
      exact ⟨(), Finset.eq_singleton_iff_unique_mem.mpr
        ⟨(hmem ()).mpr h, fun x _ => Unique.eq_default x⟩⟩
    rw [hcard]; simp [h]
  · have hcard : (Atom.level n).card = 0 := by
      rw [Finset.card_eq_zero]
      exact Finset.eq_empty_of_forall_notMem (fun x hx => h ((hmem x).mp hx))
    rw [hcard]; simp [h]

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
theorem disjSum_ogf : (A.disjSum B).ogf = A.ogf + B.ogf := by
  ext n
  simp only [map_add, coeff_ogf]
  show (A.disjSum B).count n = A.count n + B.count n
  simp only [count]
  have hL : ((A.disjSum B).level n).toLeft = A.level n := by
    ext x
    simp only [Finset.mem_toLeft, level, Set.Finite.mem_toFinset, Set.mem_setOf_eq, disjSum,
               Sum.elim_inl]
  have hR : ((A.disjSum B).level n).toRight = B.level n := by
    ext x
    simp only [Finset.mem_toRight, level, Set.Finite.mem_toFinset, Set.mem_setOf_eq, disjSum,
               Sum.elim_inr]
  have heq := Finset.card_toLeft_add_card_toRight (u := (A.disjSum B).level n)
  rw [hL, hR] at heq
  exact heq.symm

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
    refine ⟨⟨A.size a, ?_⟩, ?_, ?_⟩
    · have h : A.size a + B.size b = n := hx; omega
    · rfl
    · have h : A.size a + B.size b = n := hx; show B.size b = n - A.size a; omega

/-- OGF of Cartesian product = product of OGFs. -/
theorem cartProd_ogf : (A.cartProd B).ogf = A.ogf * B.ogf := by
  ext n
  simp only [coeff_ogf, coeff_mul]
  simp only [count]
  have hbij : ((A.cartProd B).level n).card =
      ((Finset.antidiagonal n).sigma (fun p => A.level p.1 ×ˢ B.level p.2)).card := by
    apply Finset.card_bij'
        (fun (x : A.Obj × B.Obj) _ =>
          (⟨(A.size x.1, B.size x.2), x⟩ : Σ _ : ℕ × ℕ, A.Obj × B.Obj))
        (fun y _ => y.2)
    · rintro ⟨a, b⟩ h
      have hab : A.size a + B.size b = n := by
        exact (level_mem_iff (C := A.cartProd B) (a, b)).mp h
      simp only [Finset.mem_sigma, Finset.mem_antidiagonal, Finset.mem_product]
      exact ⟨hab, (level_mem_iff (C := A) a).mpr rfl, (level_mem_iff (C := B) b).mpr rfl⟩
    · rintro ⟨⟨k, m⟩, a, b⟩ h
      simp only [Finset.mem_sigma, Finset.mem_antidiagonal, Finset.mem_product] at h
      obtain ⟨hkm, hak, hbm⟩ := h
      have ha : A.size a = k := (level_mem_iff (C := A) a).mp hak
      have hb : B.size b = m := (level_mem_iff (C := B) b).mp hbm
      show (a, b) ∈ (A.cartProd B).level n
      apply (level_mem_iff (C := A.cartProd B) (a, b)).mpr
      show A.size a + B.size b = n
      omega
    · rintro ⟨a, b⟩ _; rfl
    · rintro ⟨⟨k, m⟩, a, b⟩ h
      simp only [Finset.mem_sigma, Finset.mem_antidiagonal, Finset.mem_product] at h
      obtain ⟨-, hak, hbm⟩ := h
      have ha : A.size a = k := (level_mem_iff (C := A) a).mp hak
      have hb : B.size b = m := (level_mem_iff (C := B) b).mp hbm
      simp [ha, hb]
  rw [hbij, Finset.card_sigma]
  simp only [Finset.card_product]

/-! ## Congruence at the OGF level

Two combinatorial classes with the same counting sequence have the same OGF.
This is the bridge between combinatorial bijections and OGF identities. -/

/-- If two classes have equal counts at every level, they have equal OGFs. -/
theorem ogf_eq_of_count_eq (h : ∀ n, A.count n = B.count n) : A.ogf = B.ogf := by
  ext n
  rw [coeff_ogf, coeff_ogf, h]

/-- If level sets are equinumerous at every n, the OGFs are equal. -/
theorem ogf_eq_of_level_card_eq (h : ∀ n, (A.level n).card = (B.level n).card) :
    A.ogf = B.ogf :=
  ogf_eq_of_count_eq A B h

/-! ## Structural identities at the OGF level

The symbolic method's monoidal structure: under `cartProd`, the OGF
operation is multiplicative; under `disjSum`, additive. `Epsilon` plays
the role of multiplicative unit. -/

/-- `Epsilon × A` has the same OGF as `A` (left unit). -/
theorem Epsilon_cartProd_ogf : (Epsilon.cartProd A).ogf = A.ogf := by
  rw [cartProd_ogf, Epsilon_ogf, one_mul]

/-- `A × Epsilon` has the same OGF as `A` (right unit). -/
theorem cartProd_Epsilon_ogf : (A.cartProd Epsilon).ogf = A.ogf := by
  rw [cartProd_ogf, Epsilon_ogf, mul_one]

/-- `cartProd` is OGF-commutative. -/
theorem cartProd_comm_ogf : (A.cartProd B).ogf = (B.cartProd A).ogf := by
  rw [cartProd_ogf, cartProd_ogf, mul_comm]

/-- `cartProd` is OGF-associative. -/
theorem cartProd_assoc_ogf (C : CombinatorialClass) :
    ((A.cartProd B).cartProd C).ogf = (A.cartProd (B.cartProd C)).ogf := by
  rw [cartProd_ogf, cartProd_ogf, cartProd_ogf, cartProd_ogf, mul_assoc]

/-- `disjSum` is OGF-commutative. -/
theorem disjSum_comm_ogf : (A.disjSum B).ogf = (B.disjSum A).ogf := by
  rw [disjSum_ogf, disjSum_ogf, add_comm]

/-- `disjSum` is OGF-associative. -/
theorem disjSum_assoc_ogf (C : CombinatorialClass) :
    ((A.disjSum B).disjSum C).ogf = (A.disjSum (B.disjSum C)).ogf := by
  rw [disjSum_ogf, disjSum_ogf, disjSum_ogf, disjSum_ogf, add_assoc]

/-- Distributivity: A × (B + C) has the same OGF as (A × B) + (A × C). -/
theorem cartProd_disjSum_distrib_ogf (C : CombinatorialClass) :
    (A.cartProd (B.disjSum C)).ogf =
    ((A.cartProd B).disjSum (A.cartProd C)).ogf := by
  rw [cartProd_ogf, disjSum_ogf, disjSum_ogf, cartProd_ogf, cartProd_ogf, mul_add]

end CombinatorialClass
