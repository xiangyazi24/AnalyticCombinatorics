# Task — Plane tree OGF/EGF coefficient identities

**File:** `AnalyticCombinatorics/Examples/PlaneTrees.lean` (append)

```lean
example (n : ℕ) :
    PowerSeries.coeff n planeTreeClass.ogf = Nat.catalan n := by
  rw [coeff_ogf]
  exact planeTreeClass_count n

example (n : ℕ) :
    planeTreeClass.egf.coeff n = (Nat.catalan n : ℚ) / n.factorial := by
  rw [CombinatorialClass.coeff_egf, planeTreeClass_count]
```

Use `_root_.catalan` if `Nat.catalan` doesn't resolve.

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-plane-coeff-reply.md
