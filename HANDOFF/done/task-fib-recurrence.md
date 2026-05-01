# Task — Fibonacci recurrence theorem

**File:** `AnalyticCombinatorics/Examples/Fibonacci.lean` (append)

By analogy with the tribonacci/tetranacci/padovan recurrence theorems just landed, add:

```lean
theorem fibClass_count_recurrence (n : ℕ) :
    fibClass.count (n + 2) = fibClass.count (n + 1) + fibClass.count n := by
  sorry
```

Use whatever pattern parallels `tribClass_count_recurrence` — the file likely already has private recurrence lemmas you can expose.

Alternative if no private recurrence exists: derive from `fibClass_count_eq_fib` (which connects to `Nat.fib`) and `Nat.fib_add_two`.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-fib-recurrence-reply.md.
