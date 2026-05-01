# Task — Motzkin trees example

**File:** `AnalyticCombinatorics/Examples/MotzkinTrees.lean` (new). Add to root.

**Goal:** Define unary-binary trees (Motzkin) with internal-node size, prove finite levels, set up count.

```lean
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass

/-- Unary-binary trees: leaf, unary (one child), or binary (two children). -/
inductive MotzTree : Type
  | leaf : MotzTree
  | unary : MotzTree → MotzTree
  | binary : MotzTree → MotzTree → MotzTree

namespace MotzTree

/-- Size = number of internal (non-leaf) nodes. -/
def size : MotzTree → ℕ
  | leaf => 0
  | unary t => 1 + t.size
  | binary l r => 1 + l.size + r.size

/-- The combinatorial class of Motzkin trees. -/
noncomputable def asClass : CombinatorialClass where
  Obj := MotzTree
  size := MotzTree.size
  finite_level n := by
    induction n using Nat.strong_induction_on with
    | _ m ih =>
      cases m with
      | zero =>
        apply Set.Finite.subset (Set.finite_singleton MotzTree.leaf)
        intro t ht
        simp only [Set.mem_setOf_eq] at ht
        cases t with
        | leaf => simp [Set.mem_singleton_iff]
        | unary u => simp [size] at ht; omega
        | binary l r => simp [size] at ht; omega
      | succ k =>
        sorry  -- if too involved, file blocker
end MotzTree
```

If `finite_level` for the inductive step is hard, file a partial blocker — main payoff is the data structure being there.

## Hard constraints

- Build green
- No new sorrys when delivered (or file blocker)
- Add to root imports if file lands cleanly
- Reply at HANDOFF/outbox/task-motzkin-reply.md
