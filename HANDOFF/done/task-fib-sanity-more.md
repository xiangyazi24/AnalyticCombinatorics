# Task — Fibonacci sanity 8..12

**File:** `AnalyticCombinatorics/Examples/Fibonacci.lean` (append)

```lean
example : fibClass.count 8 = 34 := by rw [fibClass_count_eq_fib]; decide
example : fibClass.count 9 = 55 := by rw [fibClass_count_eq_fib]; decide
example : fibClass.count 10 = 89 := by rw [fibClass_count_eq_fib]; decide
example : fibClass.count 11 = 144 := by rw [fibClass_count_eq_fib]; decide
example : fibClass.count 12 = 233 := by rw [fibClass_count_eq_fib]; decide
```

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-fib-sanity-more-reply.md
