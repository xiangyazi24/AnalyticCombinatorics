# Task — Stirling 2nd Bell sanity

**File:** `AnalyticCombinatorics/Examples/SetPartitions.lean` (append)

```lean
example : ∑ k ∈ Finset.range 4, Nat.stirlingSecond 3 k = Nat.bell 3 := by
  rw [stirlingSecond_sum_eq_bell]
example : ∑ k ∈ Finset.range 5, Nat.stirlingSecond 4 k = Nat.bell 4 := by
  rw [stirlingSecond_sum_eq_bell]
example : ∑ k ∈ Finset.range 6, Nat.stirlingSecond 5 k = Nat.bell 5 := by
  rw [stirlingSecond_sum_eq_bell]
```

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-stir2-sanity-reply.md
