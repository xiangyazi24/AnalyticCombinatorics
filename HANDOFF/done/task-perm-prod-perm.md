# Task — labelProd permClass permClass count

**File:** `AnalyticCombinatorics/PartA/Ch2/LabelledClass.lean` (append)

**Goal:** Compute count of (permClass ⋆ permClass) at small n via labelProdCount.

```lean
example : CombinatorialClass.labelProdCount permClass permClass 0 = 1 := by
  unfold CombinatorialClass.labelProdCount
  simp [permClass_count_eq_factorial]

example : CombinatorialClass.labelProdCount permClass permClass 2 = 4 := by
  unfold CombinatorialClass.labelProdCount
  simp [permClass_count_eq_factorial]
  decide
```

If formula simp doesn't reduce nicely, file blocker.

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-perm-prod-perm-reply.md
