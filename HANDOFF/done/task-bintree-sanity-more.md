# Task — BinTree sanity 7, 8

**File:** `AnalyticCombinatorics/Examples/BinaryTrees.lean` (append)

Catalan: 0..8 = 1, 1, 2, 5, 14, 42, 132, 429, 1430.

```lean
example : BinTree.catalan 7 = 429 := by rw [catalan_eq_nat_catalan]; decide
example : BinTree.catalan 8 = 1430 := by rw [catalan_eq_nat_catalan]; decide
```

Use `native_decide` if needed.

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-bintree-sanity-more-reply.md
