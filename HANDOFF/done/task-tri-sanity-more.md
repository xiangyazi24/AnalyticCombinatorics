# Task — Triangulation sanity 7, 8

**File:** `AnalyticCombinatorics/Examples/Triangulations.lean` (append)

```lean
example : triangulationClass.count 7 = 429 := by
  rw [triangulationClass_count]; decide
example : triangulationClass.count 8 = 1430 := by
  rw [triangulationClass_count]; decide
```

Use `native_decide` if needed.

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-tri-sanity-more-reply.md
