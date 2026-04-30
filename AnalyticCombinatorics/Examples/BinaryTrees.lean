/-
  Analytic Combinatorics — Examples
  Binary Trees and Catalan Numbers

  A binary tree is either a leaf (size 0) or an internal node with two subtrees.
  The counting sequence satisfies C(z) = 1 + z · C(z)², giving
    Cₙ = 1/(n+1) · C(2n, n)  (the Catalan numbers)
  and the dominant singularity at z = 1/4 yields
    Cₙ ~ 4ⁿ / (n^{3/2} · √π)  as n → ∞.

  Reference: Flajolet & Sedgewick, Example I.5 and VII.2.
-/
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Nat.Choose.Basic
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass

open PowerSeries

/-- Binary trees: leaf or node with two subtrees. -/
inductive BinTree : Type
  | leaf : BinTree
  | node : BinTree → BinTree → BinTree

namespace BinTree

/-- Size of a binary tree = number of internal nodes. -/
def size : BinTree → ℕ
  | leaf       => 0
  | node l r   => 1 + size l + size r

private lemma size_leaf_eq : BinTree.leaf.size = 0 := rfl
private lemma size_node_eq (l r : BinTree) : (BinTree.node l r).size = 1 + l.size + r.size := rfl

/-- The combinatorial class of binary trees. -/
def asClass : CombinatorialClass where
  Obj   := BinTree
  size  := BinTree.size
  finite_level n := by
    induction n using Nat.strong_induction_on
    rename_i m ih
    cases m with
    | zero =>
      -- Only leaf has size 0
      apply Set.Finite.subset (Set.finite_singleton BinTree.leaf)
      intro t ht
      simp only [Set.mem_setOf_eq] at ht
      simp only [Set.mem_singleton_iff]
      cases t with
      | leaf => rfl
      | node l r =>
        simp only [size_node_eq] at ht
        omega
    | succ m =>
      -- t = node l r with l.size + r.size = m
      apply Set.Finite.subset
        (Set.finite_iUnion (fun k : Fin (m + 1) =>
          ((ih k.val k.isLt).prod
            (ih (m - k.val) (Nat.lt_succ_of_le (Nat.sub_le m k.val)))).image
          (fun p => BinTree.node p.1 p.2)))
      intro t ht
      simp only [Set.mem_setOf_eq] at ht
      cases t with
      | leaf =>
        simp only [size_leaf_eq] at ht
        omega
      | node l r =>
        simp only [size_node_eq] at ht
        have hr : BinTree.size r = m - BinTree.size l := by omega
        simp only [Set.mem_iUnion, Set.mem_image, Set.mem_prod, Set.mem_setOf_eq]
        exact ⟨⟨l.size, by omega⟩, (l, r), ⟨rfl, hr⟩, rfl⟩

/-- The Catalan number Cₙ counts binary trees with n internal nodes. -/
noncomputable def catalan (n : ℕ) : ℕ := asClass.count n

/-- The OGF C(z) satisfies the quadratic equation C = 1 + z·C². -/
theorem ogf_functional_equation :
    asClass.ogf = 1 + PowerSeries.X * asClass.ogf ^ 2 := by
  sorry

end BinTree
