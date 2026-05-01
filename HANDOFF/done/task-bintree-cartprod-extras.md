# Task — BinTree·BinTree small sanity

**File:** `AnalyticCombinatorics/Examples/BinaryTrees.lean` (append)

```lean
example : (BinTree.asClass.cartProd BinTree.asClass).count 0 = 1 := by
  rw [BinTree_asClass_cartProd_count_eq_catalan_succ]; decide
example : (BinTree.asClass.cartProd BinTree.asClass).count 1 = 2 := by
  rw [BinTree_asClass_cartProd_count_eq_catalan_succ]; decide
example : (BinTree.asClass.cartProd BinTree.asClass).count 2 = 5 := by
  rw [BinTree_asClass_cartProd_count_eq_catalan_succ]; decide
example : (BinTree.asClass.cartProd BinTree.asClass).count 3 = 14 := by
  rw [BinTree_asClass_cartProd_count_eq_catalan_succ]; decide
```

Adapt the rewrite name to whatever codex named it. Use `native_decide` if needed.

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-bintree-cartprod-extras-reply.md
