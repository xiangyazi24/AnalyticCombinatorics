# Task — BinTree³ count

**File:** `AnalyticCombinatorics/Examples/BinaryTrees.lean` (append)

**Goal:** Compute (BinTree³).count for small n.

```lean
example : ((BinTree.asClass.cartProd BinTree.asClass).cartProd BinTree.asClass).count 0 = 1 := by
  rw [CombinatorialClass.cartProd_count]
  decide

example : ((BinTree.asClass.cartProd BinTree.asClass).cartProd BinTree.asClass).count 1 = 3 := by
  rw [CombinatorialClass.cartProd_count]
  decide
```

If reduce fails, file blocker.

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-bintree-cubed-reply.md
