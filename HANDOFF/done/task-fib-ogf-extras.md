# Task — Fibonacci OGF extras

**File:** `AnalyticCombinatorics/Examples/Fibonacci.lean` (append)

```lean
example : fibClass.ogf.coeff 0 = 1 := by
  rw [coeff_ogf, fibClass_count_eq_fib]; decide
example : fibClass.ogf.coeff 5 = 8 := by
  rw [coeff_ogf, fibClass_count_eq_fib]; decide
```

Use `native_decide` if needed.

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-fib-ogf-extras-reply.md
