# Task — Stirling 2nd kind sanity at small (n,k)

**File:** `AnalyticCombinatorics/Examples/SetPartitions.lean` (append)

S(n,k) values: S(0,0)=1, S(n,0)=0 for n≥1, S(n,n)=1, S(n,1)=1, S(4,2)=7, S(5,2)=15, S(5,3)=25.

```lean
example : (CombinatorialClass.labelPow posIntClass 2).count 4 = 14 := by
  rw [labelPow_posIntClass_count_eq_factorial_mul_stirlingSecond]
  decide  -- 2! · S(4,2) = 2 · 7 = 14

example : (CombinatorialClass.labelPow posIntClass 3).count 5 = 150 := by
  rw [labelPow_posIntClass_count_eq_factorial_mul_stirlingSecond]
  decide  -- 3! · S(5,3) = 6 · 25 = 150

example : (CombinatorialClass.labelPow posIntClass 2).count 5 = 30 := by
  rw [labelPow_posIntClass_count_eq_factorial_mul_stirlingSecond]
  decide  -- 2! · S(5,2) = 2 · 15 = 30
```

Use `native_decide` if needed.

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-stirling-sanity-more-reply.md
