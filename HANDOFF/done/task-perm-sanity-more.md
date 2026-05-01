# Task — permClass sanity 8, 9, 10

**File:** `AnalyticCombinatorics/PartA/Ch2/LabelledClass.lean` (append)

```lean
example : permClass.count 8 = 40320 := by rw [permClass_count_eq_factorial]; decide
example : permClass.count 9 = 362880 := by rw [permClass_count_eq_factorial]; decide
example : permClass.count 10 = 3628800 := by rw [permClass_count_eq_factorial]; decide
```

Use `native_decide` if needed.

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-perm-sanity-more-reply.md
