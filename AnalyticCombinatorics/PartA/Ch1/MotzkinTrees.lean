/-
  Analytic Combinatorics — Part A: Symbolic Method
  Chapter I §3: Motzkin trees.

  Motzkin trees are unary-binary trees counted by nodes.  Their ordinary
  generating function satisfies M(z) = z (1 + M(z) + M(z)^2).
-/
import Mathlib.RingTheory.PowerSeries.Basic
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass

set_option linter.style.show false
set_option linter.style.nativeDecide false

open PowerSeries CombinatorialClass

/-- Motzkin trees: leaves, unary nodes, and binary nodes. -/
inductive MotzkinTree where
  | leaf : MotzkinTree
  | unary : MotzkinTree → MotzkinTree
  | binary : MotzkinTree → MotzkinTree → MotzkinTree
deriving DecidableEq, Repr

namespace MotzkinTree

/-- Size of a Motzkin tree, counted by nodes. -/
def size : MotzkinTree → ℕ
  | .leaf => 1
  | .unary t => 1 + t.size
  | .binary l r => 1 + l.size + r.size

@[simp] theorem size_leaf : size leaf = 1 := rfl

@[simp] theorem size_unary (t : MotzkinTree) : size (unary t) = 1 + size t := rfl

@[simp] theorem size_binary (l r : MotzkinTree) :
    size (binary l r) = 1 + size l + size r := rfl

/-- Every Motzkin tree has positive size. -/
theorem size_pos (t : MotzkinTree) : 1 ≤ size t := by
  cases t <;> simp [size]
  omega

/-- Level sets of Motzkin trees are finite. -/
theorem finite_size_eq (n : ℕ) : Set.Finite {t : MotzkinTree | size t = n} := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          exact Set.finite_empty.subset fun t ht => by
            have hpos := size_pos t
            simp only [Set.mem_setOf_eq] at ht
            omega
      | succ n =>
          apply Set.Finite.subset
            ((Set.finite_singleton leaf).union
              (((ih n (Nat.lt_succ_self n)).image unary).union
                (Set.finite_iUnion fun i : Fin (n + 1) =>
                  ((ih i.val i.isLt).prod (ih (n - i.val) (by omega))).image
                    (fun p => binary p.1 p.2))))
          intro t ht
          simp only [Set.mem_setOf_eq] at ht
          cases t with
          | leaf =>
              simp
          | unary u =>
              simp only [size_unary] at ht
              simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_image, Set.mem_setOf_eq]
              right
              left
              exact ⟨u, by omega, rfl⟩
          | binary l r =>
              simp only [size_binary] at ht
              have hr : size r = n - size l := by omega
              simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_image, Set.mem_iUnion,
                Set.mem_prod, Set.mem_setOf_eq]
              right
              right
              refine ⟨⟨size l, by omega⟩, (l, r), ?_, rfl⟩
              exact ⟨rfl, hr⟩

end MotzkinTree

/-- Motzkin trees as a combinatorial class, counted by nodes. -/
def motzkinTreeClass : CombinatorialClass where
  Obj := MotzkinTree
  size := MotzkinTree.size
  finite_level n := MotzkinTree.finite_size_eq n

/-- There are no Motzkin trees of size zero. -/
theorem motzkinTree_count_zero : motzkinTreeClass.count 0 = 0 := by
  simp only [CombinatorialClass.count]
  rw [Finset.card_eq_zero]
  exact Finset.eq_empty_of_forall_notMem fun t ht => by
    have hsz : MotzkinTree.size t = 0 :=
      (CombinatorialClass.level_mem_iff (C := motzkinTreeClass) t).mp ht
    have hpos := MotzkinTree.size_pos t
    omega

/-- Exactly one Motzkin tree has size one: the leaf. -/
private theorem motzkinTree_count_one_base : motzkinTreeClass.count 1 = 1 := by
  simp only [CombinatorialClass.count]
  rw [Finset.card_eq_one]
  refine ⟨MotzkinTree.leaf, Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩⟩
  · exact (CombinatorialClass.level_mem_iff (C := motzkinTreeClass) MotzkinTree.leaf).mpr rfl
  · intro t ht
    have hsz : MotzkinTree.size t = 1 :=
      (CombinatorialClass.level_mem_iff (C := motzkinTreeClass) t).mp ht
    cases t with
    | leaf => rfl
    | unary u =>
        simp only [MotzkinTree.size_unary] at hsz
        have hpos := MotzkinTree.size_pos u
        omega
    | binary l r =>
        simp only [MotzkinTree.size_binary] at hsz
        have hlpos := MotzkinTree.size_pos l
        omega

theorem motzkinTree_count_one : motzkinTreeClass.count 1 = 1 := by
  exact motzkinTree_count_one_base.trans (by native_decide)

private def motzkinToSum
    (t : MotzkinTree) :
    MotzkinTree ⊕ (Σ _ : ℕ × ℕ, MotzkinTree × MotzkinTree) :=
  match t with
  | .leaf => Sum.inl MotzkinTree.leaf
  | .unary u => Sum.inl u
  | .binary l r => Sum.inr ⟨(MotzkinTree.size l, MotzkinTree.size r), (l, r)⟩

private def sumToMotzkin
    (x : MotzkinTree ⊕ (Σ _ : ℕ × ℕ, MotzkinTree × MotzkinTree)) :
    MotzkinTree :=
  match x with
  | Sum.inl u => MotzkinTree.unary u
  | Sum.inr y => MotzkinTree.binary y.2.1 y.2.2

/-- Count recursion for non-leaf Motzkin trees. -/
theorem motzkinTree_count_succ_succ (n : ℕ) :
    motzkinTreeClass.count (n + 2) =
      motzkinTreeClass.count (n + 1) +
        ∑ p ∈ Finset.antidiagonal (n + 1),
          motzkinTreeClass.count p.1 * motzkinTreeClass.count p.2 := by
  simp only [CombinatorialClass.count]
  let binaryFs : Finset (Σ _ : ℕ × ℕ, MotzkinTree × MotzkinTree) :=
    (Finset.antidiagonal (n + 1)).sigma
      fun p => motzkinTreeClass.level p.1 ×ˢ motzkinTreeClass.level p.2
  let rhsFs : Finset (MotzkinTree ⊕ (Σ _ : ℕ × ℕ, MotzkinTree × MotzkinTree)) :=
    (motzkinTreeClass.level (n + 1)).disjSum binaryFs
  have extract : ∀ y : Σ _ : ℕ × ℕ, MotzkinTree × MotzkinTree, y ∈ binaryFs →
      y.1 ∈ Finset.antidiagonal (n + 1) ∧
      y.2.1 ∈ motzkinTreeClass.level y.1.1 ∧
      y.2.2 ∈ motzkinTreeClass.level y.1.2 := by
    intro y hy
    refine ⟨?_, ?_, ?_⟩
    · exact (Finset.mem_sigma.mp hy).1
    · exact (Finset.mem_product.mp (Finset.mem_sigma.mp hy).2).1
    · exact (Finset.mem_product.mp (Finset.mem_sigma.mp hy).2).2
  have hcard : (motzkinTreeClass.level (n + 2)).card = rhsFs.card := by
    apply Finset.card_bij'
        (fun t _ => motzkinToSum t)
        (fun x _ => sumToMotzkin x)
    · intro t ht
      have hsz : MotzkinTree.size t = n + 2 :=
        (CombinatorialClass.level_mem_iff (C := motzkinTreeClass) t).mp ht
      cases t with
      | leaf =>
          simp only [MotzkinTree.size_leaf] at hsz
          omega
      | unary u =>
          change Sum.inl u ∈ rhsFs
          apply Finset.mem_disjSum.mpr
          apply Or.inl
          refine ⟨u, ?_, rfl⟩
          apply (CombinatorialClass.level_mem_iff (C := motzkinTreeClass) u).mpr
          simp only [MotzkinTree.size_unary] at hsz
          change MotzkinTree.size u = n + 1
          omega
      | binary l r =>
          change Sum.inr ⟨(MotzkinTree.size l, MotzkinTree.size r), (l, r)⟩ ∈ rhsFs
          apply Finset.mem_disjSum.mpr
          apply Or.inr
          refine ⟨⟨(MotzkinTree.size l, MotzkinTree.size r), (l, r)⟩, ?_, rfl⟩
          apply Finset.mem_sigma.mpr
          refine ⟨?_, ?_⟩
          · apply Finset.mem_antidiagonal.mpr
            have hsum : MotzkinTree.size l + MotzkinTree.size r = n + 1 := by
              simp only [MotzkinTree.size_binary] at hsz
              omega
            exact hsum
          · apply Finset.mem_product.mpr
            exact ⟨(CombinatorialClass.level_mem_iff (C := motzkinTreeClass) l).mpr rfl,
              (CombinatorialClass.level_mem_iff (C := motzkinTreeClass) r).mpr rfl⟩
    · intro x hx
      cases x with
      | inl u =>
          have hu : u ∈ motzkinTreeClass.level (n + 1) := by
            rcases Finset.mem_disjSum.mp hx with ⟨a, ha, heq⟩ | ⟨b, hb, heq⟩
            · cases heq
              exact ha
            · cases heq
          have husz : MotzkinTree.size u = n + 1 :=
            (CombinatorialClass.level_mem_iff (C := motzkinTreeClass) u).mp hu
          apply (CombinatorialClass.level_mem_iff (C := motzkinTreeClass)
            (sumToMotzkin (Sum.inl u))).mpr
          change 1 + MotzkinTree.size u = n + 2
          omega
      | inr y =>
          have hy : y ∈ binaryFs := by
            rcases Finset.mem_disjSum.mp hx with ⟨a, ha, heq⟩ | ⟨b, hb, heq⟩
            · cases heq
            · cases heq
              exact hb
          obtain ⟨hanti, hl, hr⟩ := extract y hy
          have hl' : MotzkinTree.size y.2.1 = y.1.1 :=
            (CombinatorialClass.level_mem_iff (C := motzkinTreeClass) y.2.1).mp hl
          have hr' : MotzkinTree.size y.2.2 = y.1.2 :=
            (CombinatorialClass.level_mem_iff (C := motzkinTreeClass) y.2.2).mp hr
          have hsum : y.1.1 + y.1.2 = n + 1 := Finset.mem_antidiagonal.mp hanti
          apply (CombinatorialClass.level_mem_iff (C := motzkinTreeClass)
            (sumToMotzkin (Sum.inr y))).mpr
          change 1 + MotzkinTree.size y.2.1 + MotzkinTree.size y.2.2 = n + 2
          omega
    · intro t ht
      have hsz : MotzkinTree.size t = n + 2 :=
        (CombinatorialClass.level_mem_iff (C := motzkinTreeClass) t).mp ht
      cases t with
      | leaf =>
          simp only [MotzkinTree.size_leaf] at hsz
          omega
      | unary u => rfl
      | binary l r => rfl
    · intro x hx
      cases x with
      | inl u => rfl
      | inr y =>
          have hy : y ∈ binaryFs := by
            rcases Finset.mem_disjSum.mp hx with ⟨a, ha, heq⟩ | ⟨b, hb, heq⟩
            · cases heq
            · cases heq
              exact hb
          obtain ⟨_, hl, hr⟩ := extract y hy
          have hl' : MotzkinTree.size y.2.1 = y.1.1 :=
            (CombinatorialClass.level_mem_iff (C := motzkinTreeClass) y.2.1).mp hl
          have hr' : MotzkinTree.size y.2.2 = y.1.2 :=
            (CombinatorialClass.level_mem_iff (C := motzkinTreeClass) y.2.2).mp hr
          obtain ⟨⟨k, m⟩, l, r⟩ := y
          simp_all [motzkinToSum, sumToMotzkin]
  rw [hcard]
  change ((motzkinTreeClass.level (n + 1)).disjSum binaryFs).card =
    (motzkinTreeClass.level (n + 1)).card +
      ∑ x ∈ Finset.antidiagonal (n + 1),
        (motzkinTreeClass.level x.1).card * (motzkinTreeClass.level x.2).card
  rw [Finset.card_disjSum, Finset.card_sigma]
  apply congrArg (fun x => (motzkinTreeClass.level (n + 1)).card + x)
  apply Finset.sum_congr rfl
  intro p _
  exact Finset.card_product _ _

theorem motzkinTree_count_two : motzkinTreeClass.count 2 = 1 := by
  rw [show (2 : ℕ) = 0 + 2 by rfl, motzkinTree_count_succ_succ]
  norm_num [Finset.antidiagonal]
  rw [motzkinTree_count_zero, motzkinTree_count_one]
  native_decide

theorem motzkinTree_count_three : motzkinTreeClass.count 3 = 2 := by
  rw [show (3 : ℕ) = 1 + 2 by rfl, motzkinTree_count_succ_succ]
  norm_num [Finset.antidiagonal]
  rw [motzkinTree_count_zero, motzkinTree_count_one, motzkinTree_count_two]
  native_decide

theorem motzkinTree_count_four : motzkinTreeClass.count 4 = 4 := by
  rw [show (4 : ℕ) = 2 + 2 by rfl, motzkinTree_count_succ_succ]
  norm_num [Finset.antidiagonal]
  rw [motzkinTree_count_zero, motzkinTree_count_one, motzkinTree_count_two,
    motzkinTree_count_three]
  native_decide

theorem motzkinTree_count_five : motzkinTreeClass.count 5 = 9 := by
  rw [show (5 : ℕ) = 3 + 2 by rfl, motzkinTree_count_succ_succ]
  norm_num [Finset.antidiagonal]
  rw [motzkinTree_count_zero, motzkinTree_count_one, motzkinTree_count_two,
    motzkinTree_count_three, motzkinTree_count_four]
  native_decide

/-- The Motzkin-tree OGF satisfies `M(z) = z * (1 + M(z) + M(z)^2)`. -/
theorem motzkinTree_ogf_eq :
    motzkinTreeClass.ogf =
      PowerSeries.X * (1 + motzkinTreeClass.ogf + motzkinTreeClass.ogf ^ 2) := by
  ext n
  cases n with
  | zero =>
      rw [CombinatorialClass.coeff_ogf, motzkinTree_count_zero]
      simp
  | succ n =>
      cases n with
      | zero =>
          have hcoeff : (coeff 0) motzkinTreeClass.ogf = 0 := by
            rw [CombinatorialClass.coeff_ogf, motzkinTree_count_zero]
          have hcoeffSq : (coeff 0) (motzkinTreeClass.ogf ^ 2) = 0 := by
            rw [pow_two, coeff_mul]
            simp [CombinatorialClass.coeff_ogf, motzkinTree_count_zero, Finset.antidiagonal]
          rw [CombinatorialClass.coeff_ogf, motzkinTree_count_one,
            PowerSeries.coeff_succ_X_mul]
          simp [map_add, coeff_one, hcoeff, hcoeffSq]
      | succ n =>
          rw [CombinatorialClass.coeff_ogf, motzkinTree_count_succ_succ n,
            PowerSeries.coeff_succ_X_mul]
          simp only [map_add, coeff_one, Nat.succ_ne_zero, ↓reduceIte, zero_add,
            coeff_mul, CombinatorialClass.coeff_ogf, pow_two]
