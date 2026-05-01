# Task — BinTree cartesian product = Catalan convolution

**File:** `AnalyticCombinatorics/Examples/BinaryTrees.lean` (append)

**Goal:** Apply the general `cartProd_count` to the BinTree case and connect with Catalan.

```lean
/-- The cartesian product of two BinTree classes counts pairs of binary trees;
    the count is a Catalan convolution: ∑ p ∈ antidiag n, catalan p.1 · catalan p.2. -/
theorem BinTree_asClass_cartProd_count (n : ℕ) :
    (BinTree.asClass.cartProd BinTree.asClass).count n =
      ∑ p ∈ Finset.antidiagonal n, Nat.catalan p.1 * Nat.catalan p.2 := by
  rw [CombinatorialClass.cartProd_count]
  apply Finset.sum_congr rfl
  intro p _
  rw [show BinTree.asClass.count p.1 = Nat.catalan p.1 from BinTree.catalan_eq_nat_catalan p.1]
  rw [show BinTree.asClass.count p.2 = Nat.catalan p.2 from BinTree.catalan_eq_nat_catalan p.2]

/-- The OGF of `BinTree × BinTree` is the square of `BinTree.asClass.ogf`. -/
example : (BinTree.asClass.cartProd BinTree.asClass).ogf = BinTree.asClass.ogf ^ 2 := by
  rw [CombinatorialClass.cartProd_ogf, sq]
```

Use whatever name Mathlib's catalan resolves to in this build (we used `_root_.catalan` via `Nat.catalan` namespace in earlier files).

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-bintree-cartprod-reply.md
