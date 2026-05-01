# Task — Triangulation more sanity

**File:** `AnalyticCombinatorics/Examples/Triangulations.lean` (append)

**Goal:** Add 5, 6 sanity (Catalan 5 = 42, 6 = 132).

```lean
example : triangulationClass.count 5 = 42 := by
  rw [triangulationClass_count]; decide
example : triangulationClass.count 6 = 132 := by
  rw [triangulationClass_count]; decide
```

Use `native_decide` if needed.

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-tri-sanity-extras-reply.md
