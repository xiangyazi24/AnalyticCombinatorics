# Task — Motzkin OGF coeff form

**File:** `AnalyticCombinatorics/Examples/MotzkinTrees.lean` (append)

```lean
example (n : ℕ) :
    MotzTree.asClass.ogf.coeff n = MotzTree.asClass.count n := by
  rw [coeff_ogf]
```

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-motzkin-coeff-reply.md
