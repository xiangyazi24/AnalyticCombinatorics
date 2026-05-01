# Task — String count sanity checks

**File:** `AnalyticCombinatorics/Examples/Strings.lean` (append at end)

**Goal:** Add concrete sanity checks: number of binary strings of length n.

```lean
example : stringClass.count 0 = 1 := by rw [stringClass_count_eq_pow]; decide
example : stringClass.count 1 = 2 := by rw [stringClass_count_eq_pow]; decide
example : stringClass.count 2 = 4 := by rw [stringClass_count_eq_pow]; decide
example : stringClass.count 3 = 8 := by rw [stringClass_count_eq_pow]; decide
example : stringClass.count 4 = 16 := by rw [stringClass_count_eq_pow]; decide
example : stringClass.count 5 = 32 := by rw [stringClass_count_eq_pow]; decide
```

These may already exist (we have `stringClass.count 1 = 2`, `count 3 = 8` from earlier task). Check and add the ones missing — count 0, 2, 4, 5 are likely new.

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-string-sanity-reply.md
