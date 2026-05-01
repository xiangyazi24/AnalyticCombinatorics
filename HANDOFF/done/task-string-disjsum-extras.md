# Task — string disjSum/cartProd small sanity

**File:** `AnalyticCombinatorics/Examples/Strings.lean` (append)

```lean
example : (stringClass.disjSum stringClass).count 0 = 2 := by
  rw [CombinatorialClass.disjSum_count, stringClass_count_eq_pow]
  decide

example : (stringClass.disjSum stringClass).count 3 = 16 := by
  rw [CombinatorialClass.disjSum_count, stringClass_count_eq_pow]
  decide
```

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-string-disjsum-extras-reply.md
