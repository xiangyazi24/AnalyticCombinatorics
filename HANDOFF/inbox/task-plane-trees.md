# Task — Plane trees example

**File:** `AnalyticCombinatorics/Examples/PlaneTrees.lean` (new). Add to root.

**Goal:** Define plane trees (rooted, ordered children) and prove count of plane trees with n+1 nodes = Catalan(n). The standard bijection to binary trees.

## Required code

```lean
import AnalyticCombinatorics.Examples.BinaryTrees

/-- Plane tree: a rooted tree with an ordered sequence of children at each node.
    Equivalent to a list of subtrees. -/
inductive PlaneTree : Type
  | mk : List PlaneTree → PlaneTree
  deriving Inhabited

namespace PlaneTree

/-- Number of nodes in a plane tree. -/
def numNodes : PlaneTree → ℕ
  | mk children => 1 + (children.map numNodes).sum

end PlaneTree

/-- The combinatorial class of plane trees with n+1 nodes (size = n means n+1 actual nodes,
    indexed so that empty plane tree = "single root" → size 0). -/
noncomputable def planeTreeClass : CombinatorialClass where
  Obj := PlaneTree
  size t := t.numNodes - 1   -- size = "number of children-edges" = number of internal arcs
  finite_level n := by
    sorry
```

Hmm — the recursion looks like `PlaneTree ≃ List PlaneTree` (the children list at root). So the count of plane trees with size n equals... something Catalan-like.

A simpler/cleaner formulation: plane trees are SEQ of plane trees (the children of the root). So the combinatorial recursion is `PlaneTree(z) = z · SEQ(PlaneTree)(z) = z / (1 - PlaneTree(z))`. This gives the same Catalan-like satisfaction.

If this is too involved, **alternative**: just establish the count formula via `Tree`-style biject without proving size finiteness from scratch. Use Mathlib's existing tree machinery if any.

## Easier alternative

If the above is too involved, deliver a stub-only file with a short comment plus a sanity example of `PlaneTree` cardinality at small sizes via a Catalan reference.

```lean
/-- Plane trees and binary trees are equinumerous: PlaneTree count(n+1) = BinTree count n. 
    (Standard bijection: rotation correspondence.) -/
theorem planeTreeClass_count_eq_binTree_count (n : ℕ) :
    sorry := sorry
```

You can leave it at sketch level if a clean class definition is hard. Reply with what was achievable.

## Hard constraints

- Build green
- No new sorrys when delivered (file blocker if class definition gets stuck)
- Reply at HANDOFF/outbox/task-plane-trees-reply.md
