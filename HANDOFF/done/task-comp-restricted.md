# Task — Compositions into parts of size 1 or 2 closed form

**File:** `AnalyticCombinatorics/Examples/Fibonacci.lean` (append)

**Goal:** Prove the closed-form OGF for fibonacci compositions:

```
fibClass.ogfZ · (1 - X - X²) = 1
```

equivalently `fibClass.ogfZ = 1 / (1 - X - X²)` over ℤ[[z]].

```lean
theorem fibClass_ogfZ_mul_one_sub_X_sub_X_sq :
    ogfZ fibClass * (1 - PowerSeries.X - PowerSeries.X ^ 2) = 1 := by
  sorry  -- coefficient comparison: fibClass.count n = fib(n+1)
         -- The Fibonacci recurrence fib(n+2) = fib(n+1) + fib(n)
         -- gives the OGF satisfies (1-X-X²) · F = 1 with constant 1.
         -- For n = 0: F.coeff 0 · 1 = fib(1) · 1 = 1 ✓
         -- For n = 1: F.coeff 1 · 1 + F.coeff 0 · (-1) = fib(2) - fib(1) = 1 - 1 = 0 ✓
         -- For n = m+2: F.coeff (m+2) - F.coeff (m+1) - F.coeff m
         --            = fib(m+3) - fib(m+2) - fib(m+1) = 0 by Nat.fib_add_two
```

## Strategy (similar to compositionClass_ogfZ_mul_one_sub_two_X)

Coefficient-by-coefficient comparison using `fibClass_count_eq_fib` + `Nat.fib_add_two`.

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-comp-restricted-reply.md
- If hard, file blocker
