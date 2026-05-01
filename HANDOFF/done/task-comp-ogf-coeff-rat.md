# Task — Compositions ogfZ.coeff at 0

**File:** `AnalyticCombinatorics/Examples/Compositions.lean` (append)

```lean
example : PowerSeries.coeff 0 (CombinatorialClass.ogfZ compositionClass) = (1 : ℤ) := by
  unfold CombinatorialClass.ogfZ
  rw [PowerSeries.coeff_map, coeff_ogf, compositionClass_count_zero]
  rfl
```

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-comp-ogf-coeff-rat-reply.md
