import Mathlib

/-!
# Full ternary trees: the combinatorial object

This file introduces the genuine combinatorial object underlying the
`ternaryTreeCount` sequence of `TernaryTrees.lean`: an inductive type of full
ternary trees, the number of internal nodes (`internalSize`), the finite type
of trees of a fixed size, and the resulting count `ternaryCount`.

The closed form `ternaryCount n = binom(3n,n)/(2n+1)` is proved (via the
triple-convolution recurrence) in `TernaryTreeRecurrence.lean` and
`TernaryFussCatalan.lean`, where it is also connected to the banked
`ternaryTreeCount`.
-/

namespace AnalyticCombinatorics.Ch7.SingularityApp.TernaryTreeNS

/-- A full ternary tree: either a leaf, or an internal node with three
ordered children. -/
inductive TernaryTree where
  | leaf : TernaryTree
  | node : TernaryTree → TernaryTree → TernaryTree → TernaryTree
  deriving DecidableEq, Repr

/-- The number of internal (non-leaf) nodes of a full ternary tree. -/
def internalSize : TernaryTree → ℕ
  | .leaf => 0
  | .node l m r => internalSize l + internalSize m + internalSize r + 1

@[simp] lemma internalSize_leaf : internalSize .leaf = 0 := rfl

@[simp] lemma internalSize_node (l m r : TernaryTree) :
    internalSize (.node l m r) =
      internalSize l + internalSize m + internalSize r + 1 := rfl

/-- The full ternary trees with exactly `n` internal nodes. -/
def TernaryTreeOfSize (n : ℕ) : Type :=
  {t : TernaryTree // internalSize t = n}

instance (n : ℕ) : DecidableEq (TernaryTreeOfSize n) := by
  unfold TernaryTreeOfSize; infer_instance

end AnalyticCombinatorics.Ch7.SingularityApp.TernaryTreeNS
