# Task — Bell = ∑ Stirling 2nd identity

**File:** `AnalyticCombinatorics/Examples/SetPartitions.lean` (append)

**Goal:** Prove the standard Bell ↔ Stirling 2nd kind identity:

```lean
example (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), Nat.stirlingSecond n k = Nat.bell n := by
  sorry  -- standard identity
```

If Mathlib doesn't have this directly, prove it inductively from the recurrences.

## Hard constraints

- Build green
- No new sorrys when delivered (or file blocker if too involved)
- Reply at HANDOFF/outbox/task-stirling-second-bell-reply.md
