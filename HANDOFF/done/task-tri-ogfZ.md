# Task — Triangulation OGF quadratic identity

**File:** `AnalyticCombinatorics/Examples/Triangulations.lean` (append)

**Goal:** Lift the BinTree quadratic to triangulationClass via the alias.

```lean
/-- The triangulation class OGF satisfies the same quadratic as BinTree. -/
example :
    PowerSeries.X * (CombinatorialClass.ogfZ triangulationClass) ^ 2
      - CombinatorialClass.ogfZ triangulationClass + 1 = 0 := by
  show PowerSeries.X * (CombinatorialClass.ogfZ BinTree.asClass) ^ 2
        - CombinatorialClass.ogfZ BinTree.asClass + 1 = 0
  exact BinTree.ogfZ_quadratic
```

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-tri-ogfZ-reply.md
