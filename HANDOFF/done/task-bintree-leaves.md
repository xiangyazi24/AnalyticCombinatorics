# Task — BinTree leaf-count parameter

**File:** `AnalyticCombinatorics/Examples/BinaryTrees.lean` (append)

**Goal:** Define `numLeaves` parameter on BinTree.asClass and prove a small property.

```lean
import AnalyticCombinatorics.PartA.Ch3.Parameters

/-- Number of leaves of a binary tree. -/
def BinTree.numLeaves : BinTree → ℕ
  | leaf => 1
  | node l r => l.numLeaves + r.numLeaves

namespace BinTree

/-- `numLeaves t = size t + 1` for any binary tree. -/
theorem numLeaves_eq_size_add_one (t : BinTree) :
    t.numLeaves = t.size + 1 := by
  induction t with
  | leaf => rfl
  | node l r ih_l ih_r =>
    simp [numLeaves, size, ih_l, ih_r]; omega

/-- As a Parameter on asClass: numLeaves a = a.size + 1. -/
def numLeavesParam : Parameter asClass := numLeaves

/-- jointCount of (size, leaves) is just count when k = n+1, else 0. -/
example (n : ℕ) :
    asClass.jointCount numLeavesParam n (n + 1) = asClass.count n := by
  unfold CombinatorialClass.jointCount
  rw [Finset.filter_eq_self.mpr]
  intro a _
  exact (numLeaves_eq_size_add_one a)

end BinTree
```

If precise lemmas need adjustment, simplify; main payoff is the leaf count = size + 1 identity.

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-bintree-leaves-reply.md
