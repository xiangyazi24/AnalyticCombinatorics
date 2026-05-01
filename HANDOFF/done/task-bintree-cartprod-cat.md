# Task — BinTree·BinTree convolution = catalan(n+1)

**File:** `AnalyticCombinatorics/Examples/BinaryTrees.lean` (append)

**Goal:** Note that the Catalan convolution gives catalan(n+1) (since C(z)² = (C-1)/X).

```lean
example (n : ℕ) :
    (BinTree.asClass.cartProd BinTree.asClass).count n = Nat.catalan (n + 1) := by
  sorry  -- standard Catalan convolution identity
```

If Mathlib's `catalan` recurrence directly gives this, use it. Else file blocker.

## Hard constraints

- Build green
- No new sorrys when delivered (or file blocker)
- Reply at HANDOFF/outbox/task-bintree-cartprod-cat-reply.md
