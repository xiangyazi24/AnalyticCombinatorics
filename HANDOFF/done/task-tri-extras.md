# Task — Triangulation extras (closed-form via centralBinom)

**File:** `AnalyticCombinatorics/Examples/Triangulations.lean` (append)

**Goal:** Lift the BinTree-side closed form via the `triangulationClass = BinTree.asClass` alias.

```lean
import Mathlib.Data.Nat.Choose.Central

/-- (n+1) · #triangulations of (n+2)-gon = C(2n, n) (central binomial). -/
theorem succ_mul_triangulationClass_count_eq_centralBinom (n : ℕ) :
    (n + 1) * triangulationClass.count n = n.centralBinom := by
  exact BinTree.succ_mul_catalan_eq_centralBinom n

/-- Closed form: #triangulations of (n+2)-gon = C(2n,n) / (n+1). -/
theorem triangulationClass_count_eq_centralBinom_div (n : ℕ) :
    triangulationClass.count n = n.centralBinom / (n + 1) := by
  exact BinTree.catalan_eq_centralBinom_div n
```

These are direct re-exports of the BinTree theorems via the alias.

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-tri-extras-reply.md
