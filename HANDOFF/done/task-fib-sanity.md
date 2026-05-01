# Task — Fibonacci sanity checks

**File:** `AnalyticCombinatorics/Examples/Fibonacci.lean` (append at end)

**Goal:** Add concrete sanity checks: fibClass.count = 1, 1, 2, 3, 5, 8, 13, ...

```lean
/-! Sanity checks: fib(n+1) sequence is 1, 1, 2, 3, 5, 8, 13, 21, 34, 55. -/
example : fibClass.count 0 = 1 := by rw [fibClass_count_eq_fib]; decide
example : fibClass.count 1 = 1 := by rw [fibClass_count_eq_fib]; decide
example : fibClass.count 2 = 2 := by rw [fibClass_count_eq_fib]; decide
example : fibClass.count 3 = 3 := by rw [fibClass_count_eq_fib]; decide
example : fibClass.count 4 = 5 := by rw [fibClass_count_eq_fib]; decide
example : fibClass.count 5 = 8 := by rw [fibClass_count_eq_fib]; decide
example : fibClass.count 6 = 13 := by rw [fibClass_count_eq_fib]; decide
example : fibClass.count 7 = 21 := by rw [fibClass_count_eq_fib]; decide
```

Use `native_decide` if `decide` is too slow.

## Hard constraints

- Build green
- Reply at HANDOFF/outbox/task-fib-sanity-reply.md
