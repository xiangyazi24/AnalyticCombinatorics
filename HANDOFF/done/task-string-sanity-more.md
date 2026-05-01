# Task — Strings sanity 6..10

**File:** `AnalyticCombinatorics/Examples/Strings.lean` (append)

```lean
example : stringClass.count 6 = 64 := stringClass_count_eq_pow 6
example : stringClass.count 7 = 128 := stringClass_count_eq_pow 7
example : stringClass.count 8 = 256 := stringClass_count_eq_pow 8
example : stringClass.count 9 = 512 := stringClass_count_eq_pow 9
example : stringClass.count 10 = 1024 := stringClass_count_eq_pow 10
```

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-string-sanity-more-reply.md
