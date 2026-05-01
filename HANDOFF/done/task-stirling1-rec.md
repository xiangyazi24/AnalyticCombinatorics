# Task — Stirling 1st kind classical recurrence

**File:** `AnalyticCombinatorics/Examples/SetPartitions.lean` (append)

The unsigned Stirling 1st kind recurrence: `c(n+1, k+1) = n · c(n, k+1) + c(n, k)` (where `c` is the unsigned form, what Mathlib likely calls `Nat.stirlingFirst`).

Try to **state and prove**:

```lean
theorem stirlingFirst_succ (n k : ℕ) :
    Nat.stirlingFirst (n + 1) (k + 1) = n * Nat.stirlingFirst n (k + 1) + Nat.stirlingFirst n k := by
  sorry
```

Almost certainly already in Mathlib as `Nat.stirlingFirst_succ_succ` or similar. Search first; expose if found, document blocker if not.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-stirling1-rec-reply.md.
- Do NOT introduce axioms.
