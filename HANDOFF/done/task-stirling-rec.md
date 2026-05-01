# Task — Stirling 2nd kind classical recurrence

**File:** `AnalyticCombinatorics/Examples/SetPartitions.lean` (append)

The classical recurrence: `S(n+1, k) = k · S(n, k) + S(n, k-1)` (with appropriate edge cases).

Try to **state and prove** for `Nat.stirlingSecond` (or whatever name Mathlib uses):

```lean
theorem stirlingSecond_succ (n k : ℕ) :
    Nat.stirlingSecond (n + 1) (k + 1) = (k + 1) * Nat.stirlingSecond n (k + 1) + Nat.stirlingSecond n k := by
  sorry
```

This is almost certainly already in Mathlib under `Nat.stirlingSecond_succ_succ` or similar. Search first; if it exists, just expose. If not, **document the absence** and stop.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-stirling-rec-reply.md.
- If Mathlib has it under a different name, expose under a project-friendly name (don't reprove).
- Do NOT introduce axioms.
