# Task — BinTree OGF coeff = catalan

**File:** `AnalyticCombinatorics/Examples/BinaryTrees.lean` (append)

**Goal:** Direct OGF coefficient form.

```lean
example (n : ℕ) :
    PowerSeries.coeff n (BinTree.asClass.ogf) = Nat.catalan n := by
  rw [coeff_ogf]
  exact BinTree.catalan_eq_nat_catalan n
```

Use whatever Catalan name fits this build (root-level `catalan` may be needed).

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-bintree-ogf-coeff-reply.md
