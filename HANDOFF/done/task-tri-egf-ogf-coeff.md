# Task — Triangulation OGF/EGF coefficient identities

**File:** `AnalyticCombinatorics/Examples/Triangulations.lean` (append)

```lean
example (n : ℕ) :
    PowerSeries.coeff n triangulationClass.ogf = Nat.catalan n := by
  rw [show triangulationClass.ogf = BinTree.asClass.ogf from rfl, coeff_ogf]
  exact BinTree.catalan_eq_nat_catalan n

example (n : ℕ) :
    triangulationClass.egf.coeff n = (Nat.catalan n : ℚ) / n.factorial := by
  show BinTree.asClass.egf.coeff n = _
  rw [CombinatorialClass.coeff_egf]
  rw [show (BinTree.asClass.count n : ℕ) = Nat.catalan n from
        BinTree.catalan_eq_nat_catalan n]
```

Use `_root_.catalan` if `Nat.catalan` doesn't resolve.

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-tri-egf-ogf-coeff-reply.md
