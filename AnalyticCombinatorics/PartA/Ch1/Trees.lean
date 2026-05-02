/-
  Analytic Combinatorics — Part A: Symbolic Method
  Chapter I §3: Tree equations and ordinary generating functions.

  This file formalizes the Catalan binary-tree equation
      T = epsilon + Z × T × T
  and its OGF form
      T(z) = 1 + z T(z)^2.
-/
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Nat.Choose.Central
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass

set_option linter.style.show false
set_option linter.style.nativeDecide false

open PowerSeries CombinatorialClass

/-- Binary trees counted by internal nodes. -/
inductive BinaryTree where
  | leaf : BinaryTree
  | node : BinaryTree → BinaryTree → BinaryTree
deriving DecidableEq, Repr

namespace BinaryTree

/-- Size of a binary tree: leaves have size 0, nodes contribute 1. -/
def size : BinaryTree → ℕ
  | leaf => 0
  | node l r => 1 + size l + size r

/-- A computable finite list of all binary trees of a fixed size. -/
def ofSize (n : ℕ) : Finset BinaryTree :=
  match n with
  | 0 => {leaf}
  | n + 1 =>
      ((Finset.antidiagonal n).attach.sigma fun p => ofSize p.1.1 ×ˢ ofSize p.1.2).image
        fun x => node x.2.1 x.2.2
termination_by n
decreasing_by
  all_goals
    have hp := Finset.mem_antidiagonal.mp p.2
    omega

/-- The finite construction `ofSize n` contains exactly the trees of size `n`. -/
theorem mem_ofSize_iff {t : BinaryTree} {n : ℕ} : t ∈ ofSize n ↔ size t = n := by
  revert t
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro t
      cases n with
      | zero =>
          cases t <;> simp [ofSize, size]
      | succ n =>
          cases t with
          | leaf =>
              simp [ofSize, size]
          | node l r =>
              constructor
              · intro ht
                simp only [ofSize, Finset.mem_image, Finset.mem_sigma, Finset.mem_product,
                  Finset.mem_attach] at ht
                obtain ⟨x, hx, hnode⟩ := ht
                obtain ⟨_, hl, hr⟩ := hx
                cases x with
                | mk p lr =>
                    cases p with
                    | mk p hp =>
                    cases lr with
                    | mk l' r' =>
                        simp only at hnode
                        cases hnode
                        have hp' : p.1 + p.2 = n := Finset.mem_antidiagonal.mp hp
                        have hpl : p.1 < n + 1 := by omega
                        have hpr : p.2 < n + 1 := by omega
                        have hlsz : size l = p.1 := (ih p.1 hpl (t := l)).mp hl
                        have hrsz : size r = p.2 := (ih p.2 hpr (t := r)).mp hr
                        simp only [size]
                        omega
              · intro hsz
                simp only [ofSize, Finset.mem_image, Finset.mem_sigma, Finset.mem_product,
                  Finset.mem_attach]
                have hp : (size l, size r) ∈ Finset.antidiagonal n := by
                  simp only [Finset.mem_antidiagonal]
                  simp only [size] at hsz
                  omega
                refine ⟨⟨⟨(size l, size r), hp⟩, (l, r)⟩, ?_, rfl⟩
                refine ⟨?_, ?_, ?_⟩
                · trivial
                · have hltn : size l < n + 1 := by
                    simp only [size] at hsz
                    omega
                  exact (ih (size l) hltn (t := l)).mpr rfl
                · have hrtn : size r < n + 1 := by
                    simp only [size] at hsz
                    omega
                  exact (ih (size r) hrtn (t := r)).mpr rfl

end BinaryTree

/-- Binary trees as a combinatorial class, counted by internal nodes. -/
def binaryTreeClass : CombinatorialClass where
  Obj := BinaryTree
  size := BinaryTree.size
  finite_level n := by
    exact Set.Finite.ofFinset (BinaryTree.ofSize n) fun t => by
      change t ∈ BinaryTree.ofSize n ↔ BinaryTree.size t = n
      exact BinaryTree.mem_ofSize_iff

/-- The abstract level set agrees with the explicit finite construction. -/
theorem binaryTreeClass_level_eq (n : ℕ) :
    binaryTreeClass.level n = BinaryTree.ofSize n := by
  ext t
  rw [CombinatorialClass.level_mem_iff]
  exact BinaryTree.mem_ofSize_iff.symm

/-- Counts can be computed from the explicit finite construction. -/
theorem binaryTreeClass_count_eq_card (n : ℕ) :
    binaryTreeClass.count n = (BinaryTree.ofSize n).card := by
  rw [CombinatorialClass.count, binaryTreeClass_level_eq]
  rfl

private def binaryTreeToSigma (t : BinaryTree) : Σ _ : ℕ × ℕ, BinaryTree × BinaryTree :=
  match t with
  | BinaryTree.leaf => ⟨(0, 0), (BinaryTree.leaf, BinaryTree.leaf)⟩
  | BinaryTree.node l r => ⟨(BinaryTree.size l, BinaryTree.size r), (l, r)⟩

private def sigmaToBinaryTree (y : Σ _ : ℕ × ℕ, BinaryTree × BinaryTree) : BinaryTree :=
  BinaryTree.node y.2.1 y.2.2

private theorem sigmaToBinaryTree_binaryTreeToSigma (t : BinaryTree)
    (h : t ≠ BinaryTree.leaf) : sigmaToBinaryTree (binaryTreeToSigma t) = t := by
  cases t with
  | leaf => exact (h rfl).elim
  | node l r => rfl

/-- The Catalan convolution at the count level. -/
theorem binaryTree_count_recursion (n : ℕ) :
    binaryTreeClass.count (n + 1) =
      ∑ p ∈ Finset.antidiagonal n, binaryTreeClass.count p.1 * binaryTreeClass.count p.2 := by
  simp only [CombinatorialClass.count]
  let rhsFs : Finset (Σ _ : ℕ × ℕ, BinaryTree × BinaryTree) :=
    (Finset.antidiagonal n).sigma
      fun p => binaryTreeClass.level p.1 ×ˢ binaryTreeClass.level p.2
  have extract : ∀ y : Σ _ : ℕ × ℕ, BinaryTree × BinaryTree, y ∈ rhsFs →
      y.1 ∈ Finset.antidiagonal n ∧
      y.2.1 ∈ binaryTreeClass.level y.1.1 ∧
      y.2.2 ∈ binaryTreeClass.level y.1.2 := by
    intro y hy
    refine ⟨?_, ?_, ?_⟩
    · exact (Finset.mem_sigma.mp hy).1
    · exact (Finset.mem_product.mp (Finset.mem_sigma.mp hy).2).1
    · exact (Finset.mem_product.mp (Finset.mem_sigma.mp hy).2).2
  have hcard : (binaryTreeClass.level (n + 1)).card = rhsFs.card := by
    apply Finset.card_bij'
        (fun t _ => binaryTreeToSigma t)
        (fun y _ => sigmaToBinaryTree y)
    · intro t ht
      have hsz : BinaryTree.size t = n + 1 :=
        (CombinatorialClass.level_mem_iff (C := binaryTreeClass) t).mp ht
      cases t with
      | leaf =>
          simp only [BinaryTree.size] at hsz
          omega
      | node l r =>
          change ⟨(BinaryTree.size l, BinaryTree.size r), (l, r)⟩ ∈ rhsFs
          apply Finset.mem_sigma.mpr
          refine ⟨?_, ?_⟩
          · simp only [Finset.mem_antidiagonal]
            simp only [BinaryTree.size] at hsz
            omega
          · apply Finset.mem_product.mpr
            exact ⟨(CombinatorialClass.level_mem_iff (C := binaryTreeClass) l).mpr rfl,
              (CombinatorialClass.level_mem_iff (C := binaryTreeClass) r).mpr rfl⟩
    · intro y hy
      obtain ⟨hanti, hl, hr⟩ := extract y hy
      have hl' : BinaryTree.size y.2.1 = y.1.1 :=
        (CombinatorialClass.level_mem_iff (C := binaryTreeClass) y.2.1).mp hl
      have hr' : BinaryTree.size y.2.2 = y.1.2 :=
        (CombinatorialClass.level_mem_iff (C := binaryTreeClass) y.2.2).mp hr
      have hsum : y.1.1 + y.1.2 = n := Finset.mem_antidiagonal.mp hanti
      apply (CombinatorialClass.level_mem_iff (C := binaryTreeClass)
        (sigmaToBinaryTree y)).mpr
      change 1 + BinaryTree.size y.2.1 + BinaryTree.size y.2.2 = n + 1
      omega
    · intro t ht
      have hsz : BinaryTree.size t = n + 1 :=
        (CombinatorialClass.level_mem_iff (C := binaryTreeClass) t).mp ht
      have hne : t ≠ BinaryTree.leaf := by
        intro htleaf
        rw [htleaf] at hsz
        simp only [BinaryTree.size] at hsz
        omega
      exact sigmaToBinaryTree_binaryTreeToSigma t hne
    · intro y hy
      obtain ⟨hanti, hl, hr⟩ := extract y hy
      have hl' : BinaryTree.size y.2.1 = y.1.1 :=
        (CombinatorialClass.level_mem_iff (C := binaryTreeClass) y.2.1).mp hl
      have hr' : BinaryTree.size y.2.2 = y.1.2 :=
        (CombinatorialClass.level_mem_iff (C := binaryTreeClass) y.2.2).mp hr
      obtain ⟨⟨k, m⟩, l, r⟩ := y
      simp_all [binaryTreeToSigma, sigmaToBinaryTree]
  rw [hcard, Finset.card_sigma]
  apply Finset.sum_congr rfl
  intro p _
  exact Finset.card_product _ _

/-- The binary-tree OGF satisfies `T(z) = 1 + z * T(z)^2` over `ℕ[[z]]`. -/
theorem binaryTree_ogf_eq :
    binaryTreeClass.ogf = 1 + X * binaryTreeClass.ogf ^ 2 := by
  ext n
  cases n with
  | zero =>
      rw [CombinatorialClass.coeff_ogf]
      simp [binaryTreeClass_count_eq_card, BinaryTree.ofSize]
  | succ n =>
      rw [CombinatorialClass.coeff_ogf, binaryTree_count_recursion n]
      simp only [map_add, coeff_one, Nat.succ_ne_zero, ↓reduceIte, zero_add,
        PowerSeries.coeff_succ_X_mul]
      rw [pow_two, PowerSeries.coeff_mul]
      simp only [CombinatorialClass.coeff_ogf]

/-! ## Sanity checks -/

theorem binaryTree_count_zero : binaryTreeClass.count 0 = 1 := by
  rw [binaryTreeClass_count_eq_card]
  native_decide

theorem binaryTree_count_one : binaryTreeClass.count 1 = 1 := by
  rw [binaryTreeClass_count_eq_card]
  native_decide

theorem binaryTree_count_two : binaryTreeClass.count 2 = 2 := by
  rw [binaryTreeClass_count_eq_card]
  native_decide

theorem binaryTree_count_three : binaryTreeClass.count 3 = 5 := by
  rw [binaryTreeClass_count_eq_card]
  native_decide

theorem binaryTree_count_four : binaryTreeClass.count 4 = 14 := by
  rw [binaryTreeClass_count_eq_card]
  native_decide

/-! ## Initial Catalan values via the central-binomial formula. -/

theorem binaryTree_count_catalan_zero :
    binaryTreeClass.count 0 = Nat.centralBinom 0 / (0 + 1) := by
  rw [binaryTree_count_zero]
  decide

theorem binaryTree_count_catalan_one :
    binaryTreeClass.count 1 = Nat.centralBinom 1 / (1 + 1) := by
  rw [binaryTree_count_one]
  decide

theorem binaryTree_count_catalan_two :
    binaryTreeClass.count 2 = Nat.centralBinom 2 / (2 + 1) := by
  rw [binaryTree_count_two]
  decide

theorem binaryTree_count_catalan_three :
    binaryTreeClass.count 3 = Nat.centralBinom 3 / (3 + 1) := by
  rw [binaryTree_count_three]
  decide

theorem binaryTree_count_catalan_four :
    binaryTreeClass.count 4 = Nat.centralBinom 4 / (4 + 1) := by
  rw [binaryTree_count_four]
  decide
