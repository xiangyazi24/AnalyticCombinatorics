# Task — Fib OGF coeff closed form (via fib(n+1))

**File:** `AnalyticCombinatorics/Examples/Fibonacci.lean` (append)

**Goal:** Add closed-form coefficient identity.

```lean
/-- The OGF of Fibonacci compositions has [zⁿ] = fib(n+1). -/
theorem fibClass_ogfZ_coeff (n : ℕ) :
    PowerSeries.coeff n (ogfZ fibClass) = (Nat.fib (n + 1) : ℤ) := by
  unfold ogfZ
  rw [PowerSeries.coeff_map, coeff_ogf, fibClass_count_eq_fib]
  push_cast
  rfl
```

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-fib-ogf-coeff-reply.md
