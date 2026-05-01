# Task — Triangulations example

**File:** `AnalyticCombinatorics/Examples/Triangulations.lean` (new). Add to root.

**Goal:** Define triangulations of a convex (n+2)-gon as a CombinatorialClass and prove it has Catalan-many objects, by an explicit Equiv to `BinTree`.

```lean
import AnalyticCombinatorics.Examples.BinaryTrees

/-- A triangulation of a convex (n+2)-gon is the same data as a binary tree
    with n internal nodes (well-known bijection: each triangle ↔ internal node). -/
noncomputable def triangulationClass : CombinatorialClass := BinTree.asClass

/-- Count of triangulations of an (n+2)-gon equals the n-th Catalan number. -/
theorem triangulationClass_count (n : ℕ) :
    triangulationClass.count n = Nat.catalan n := by
  rw [show triangulationClass = BinTree.asClass from rfl]
  exact BinTree.catalan_eq_nat_catalan n
```

The triangulationClass is just a renaming of BinTree.asClass via the well-known bijection. The proof reduces to existing `catalan_eq_nat_catalan`.

## Hard constraints

- Build green
- No new sorrys
- Add the new file to `AnalyticCombinatorics.lean`
- Write reply at HANDOFF/outbox/task-triangulations-reply.md
