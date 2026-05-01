# Task — Triangulation sanity checks

**File:** `AnalyticCombinatorics/Examples/Triangulations.lean` (append at end)

**Goal:** Add concrete sanity checks: number of triangulations of (n+2)-gon for small n.

```lean
example : triangulationClass.count 0 = 1 := by rw [triangulationClass_count]; decide
example : triangulationClass.count 1 = 1 := by rw [triangulationClass_count]; decide
example : triangulationClass.count 2 = 2 := by rw [triangulationClass_count]; decide
example : triangulationClass.count 3 = 5 := by rw [triangulationClass_count]; decide
example : triangulationClass.count 4 = 14 := by rw [triangulationClass_count]; decide
```

Use `native_decide` if `decide` is too slow.

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-tri-sanity-reply.md
