# Task — Fibonacci rational EGF coefficient

**File:** `AnalyticCombinatorics/Examples/Fibonacci.lean` (append)

**Goal:** Direct EGF coefficient identity.

```lean
example (n : ℕ) :
    fibClass.egf.coeff n = (Nat.fib (n + 1) : ℚ) / n.factorial := by
  rw [CombinatorialClass.coeff_egf, fibClass_count_eq_fib]
```

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-fib-egf-coeff-reply.md
