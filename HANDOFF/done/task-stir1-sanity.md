# Task — Stirling 1st sanity

**File:** `AnalyticCombinatorics/Examples/SetPartitions.lean` (append)

Stirling 1st kind first row: c(0,0)=1; c(n,0)=0 for n≥1; c(n,n)=1; c(3,1)=2; c(4,2)=11; c(5,3)=35.

```lean
example : ∑ k ∈ Finset.range 4, Nat.stirlingFirst 3 k = 6 := by
  rw [stirlingFirst_sum_eq_factorial]; decide

example : ∑ k ∈ Finset.range 5, Nat.stirlingFirst 4 k = 24 := by
  rw [stirlingFirst_sum_eq_factorial]; decide

example : ∑ k ∈ Finset.range 6, Nat.stirlingFirst 5 k = 120 := by
  rw [stirlingFirst_sum_eq_factorial]; decide
```

Use `native_decide` if needed.

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-stir1-sanity-reply.md
