# Task — BinTree EGF coeff = catalan/n!

**File:** `AnalyticCombinatorics/Examples/BinaryTrees.lean` (append at end)

**Goal:** Add the rational EGF coefficient form for BinTree (= catalan n / n!).

```lean
/-- Rational EGF coefficient: [zⁿ] BinTree.asClass.egf = catalan n / n!. -/
example (n : ℕ) :
    BinTree.asClass.egf.coeff n = (Nat.catalan n : ℚ) / n.factorial := by
  rw [CombinatorialClass.coeff_egf]
  -- count = catalan via BinTree.catalan_eq_nat_catalan
  show (BinTree.asClass.count n : ℚ) / n.factorial = (Nat.catalan n : ℚ) / n.factorial
  rw [show (BinTree.asClass.count n : ℕ) = Nat.catalan n from
        BinTree.catalan_eq_nat_catalan n]
```

If `Nat.catalan` doesn't exist (Mathlib uses root-level `catalan`), use that name.

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-bintree-egf-coeff-reply.md
