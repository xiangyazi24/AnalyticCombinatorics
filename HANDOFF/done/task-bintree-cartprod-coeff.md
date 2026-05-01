# Task — BinTree cartProd coefficient sanity

**File:** `AnalyticCombinatorics/Examples/BinaryTrees.lean` (append)

```lean
example : (BinTree.asClass.cartProd BinTree.asClass).count 0 = 1 := by
  rw [BinTree_asClass_cartProd_count]
  decide  -- ∑ p ∈ antidiag 0, catalan p.1 · catalan p.2 = 1·1 = 1

example : (BinTree.asClass.cartProd BinTree.asClass).count 2 = 4 := by
  rw [BinTree_asClass_cartProd_count]
  decide  -- 1·2 + 1·1 + 2·1 = 5? wait: catalan = 1,1,2 so antidiag 2 = (0,2),(1,1),(2,0)
          -- 1·2 + 1·1 + 2·1 = 5
```

Adapt expected value if needed (it should be ∑ catalan_i · catalan_{n-i} for n=2 = catalan(3) = 5 by Catalan convolution). Use `native_decide`.

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-bintree-cartprod-coeff-reply.md
