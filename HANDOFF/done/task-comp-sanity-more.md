# Task — Compositions sanity 8, 10, 12

**File:** `AnalyticCombinatorics/Examples/Compositions.lean` (append)

```lean
example : compositionClass.count 8 = 128 := compositionClass_count_succ 7
example : compositionClass.count 10 = 512 := compositionClass_count_succ 9
example : compositionClass.count 12 = 2048 := compositionClass_count_succ 11
```

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-comp-sanity-more-reply.md
