/-
  Analytic Combinatorics — Examples
  Binary Trees and Catalan Numbers

  A binary tree is either a leaf (size 0) or an internal node with two subtrees.
  The counting sequence satisfies C(z) = 1 + z · C(z)², giving
    Cₙ = (1/n+1) · C(2n, n)  (the Catalan numbers)
  and the dominant singularity at z = 1/4 yields
    Cₙ ~ 4ⁿ / (n^{3/2} · √π)  as n → ∞.

  Reference: Flajolet & Sedgewick, Example I.5 and VII.2.
-/
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Nat.Choose.Basic
import AnalyticCombinatorics.SymbolicMethod.CombinatorialClass

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

/-- The combinatorial class of binary trees. -/
def asClass : CombinatorialClass where
  Obj   := BinTree
  size  := BinTree.size
  finite_level n := by
    apply Set.finite_range_of_finite_preimage
    sorry -- finite_level: needs induction on tree structure

/-- The Catalan number Cₙ counts binary trees with n internal nodes. -/
def catalan (n : ℕ) : ℕ := (asClass.count n)

-- The functional equation C(z) = 1 + z · C(z)² characterizes the OGF.
-- This is the key structural equation from the symbolic method.

/-- The OGF C(z) satisfies the quadratic equation C = 1 + z·C². -/
theorem ogf_functional_equation :
    asClass.ogf = 1 + PowerSeries.X * asClass.ogf ^ 2 := by
  sorry

end BinTree
