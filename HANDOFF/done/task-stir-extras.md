# Task — small Stirling values direct compute

**File:** `AnalyticCombinatorics/Examples/SetPartitions.lean` (append)

```lean
example : Nat.stirlingSecond 4 2 = 7 := by decide
example : Nat.stirlingSecond 5 3 = 25 := by decide
example : Nat.stirlingFirst 4 2 = 11 := by decide
example : Nat.stirlingFirst 5 3 = 35 := by decide
```

Use `native_decide` if needed.

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-stir-extras-reply.md
