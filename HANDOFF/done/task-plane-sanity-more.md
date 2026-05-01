# Task — Plane tree sanity 7, 8

**File:** `AnalyticCombinatorics/Examples/PlaneTrees.lean` (append)

```lean
example : planeTreeClass.count 7 = 429 := by
  rw [planeTreeClass_count]; decide
example : planeTreeClass.count 8 = 1430 := by
  rw [planeTreeClass_count]; decide
```

Use `native_decide` if needed.

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-plane-sanity-more-reply.md
