# Task — Plane trees more sanity

**File:** `AnalyticCombinatorics/Examples/PlaneTrees.lean` (append)

**Goal:** Add catalan 5 = 42 and catalan 6 = 132 sanity for plane trees.

```lean
example : planeTreeClass.count 5 = 42 := by rw [planeTreeClass_count]; decide
example : planeTreeClass.count 6 = 132 := by rw [planeTreeClass_count]; decide
```

If `decide` is slow, use `native_decide`.

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-plane-tree-sanity-reply.md
