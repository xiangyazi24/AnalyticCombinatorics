# Task — Stirling 1st kind connection to permutations

**File:** `AnalyticCombinatorics/Examples/SetPartitions.lean` (append) or new file as appropriate.

**Goal:** Add a connection theorem: ∑_k Stirling 1st(n, k) = n!.

```lean
example (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), Nat.stirlingFirst n k = n.factorial := by
  sorry  -- known identity; check Mathlib for sum_stirlingFirst or similar
```

If Mathlib has the identity, restate or apply directly. If not, file blocker.

## Hard constraints

- Build green
- No new sorrys when delivered (or file blocker)
- Reply at HANDOFF/outbox/task-stirling-first-perm-reply.md
