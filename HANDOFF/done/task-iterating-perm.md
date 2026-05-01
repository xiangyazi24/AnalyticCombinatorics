# Task — labelPow permClass count formula

**File:** `AnalyticCombinatorics/PartA/Ch2/LabelledClass.lean` (append)

**Goal:** Compute `(labelPow permClass k).count n` formula and small sanity.

```lean
example : (CombinatorialClass.labelPow permClass 0).count 0 = 1 := by
  simp [CombinatorialClass.labelPow, Epsilon_count_zero]

example : (CombinatorialClass.labelPow permClass 0).count 1 = 0 := by
  simp [CombinatorialClass.labelPow]
  rw [Epsilon_count_pos]; · rfl; · omega

example : (CombinatorialClass.labelPow permClass 1).count 1 = 1 := by
  simp [CombinatorialClass.labelPow]
  -- labelPow permClass 1 = permClass.labelProd Epsilon
  -- count 1 = ∑ (1 choose k) · perm.count k · ε.count (1-k)
  --        = (1 choose 1) · 1 · 1 = 1
  sorry
```

If too involved, file blocker.

## Hard constraints

- Build green
- No new sorrys when delivered (or file blocker)
- Reply at HANDOFF/outbox/task-iterating-perm-reply.md
