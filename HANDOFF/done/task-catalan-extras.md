# Task — Catalan extras

**File:** `AnalyticCombinatorics/Examples/BinaryTrees.lean` (append after the existing sanity examples)

**Goal:** Add more Catalan number sanity checks and a structural identity.

```lean
example : BinTree.catalan 4 = 14 := by rw [catalan_eq_nat_catalan]; decide
example : BinTree.catalan 5 = 42 := by rw [catalan_eq_nat_catalan]; decide
example : BinTree.catalan 6 = 132 := by rw [catalan_eq_nat_catalan]; decide

/-- The dominant root of the Catalan generating function quadratic
    1 + z·C² - C = 0 satisfies C(0) = 1. -/
example : asClass.ogf.coeff 0 = 1 := by
  show asClass.count 0 = 1
  exact count_zero
```

Adapt as needed (decide may not close immediately for catalan 6 if reduction is slow — try `native_decide`).

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-catalan-extras-reply.md
