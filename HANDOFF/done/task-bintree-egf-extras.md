# Task — BinTree EGF small sanity

**File:** `AnalyticCombinatorics/Examples/BinaryTrees.lean` (append)

```lean
example : BinTree.asClass.egf.coeff 0 = 1 := by
  rw [CombinatorialClass.coeff_egf]
  rw [show (BinTree.asClass.count 0 : ℕ) = 1 from BinTree.count_zero]
  simp

example : BinTree.asClass.egf.coeff 2 = (2 : ℚ) / 2 := by
  rw [CombinatorialClass.coeff_egf]
  rw [show (BinTree.asClass.count 2 : ℕ) = 2 from by
        rw [BinTree.catalan_eq_nat_catalan]; decide]
  simp [Nat.factorial]
```

Adapt as needed.

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-bintree-egf-extras-reply.md
