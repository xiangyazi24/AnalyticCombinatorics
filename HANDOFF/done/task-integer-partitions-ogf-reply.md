Done.

Created `AnalyticCombinatorics/PartA/Ch1/IntPartTheory.lean`.

Verification:

```text
lake build AnalyticCombinatorics.PartA.Ch1.IntPartTheory
Build completed successfully (1388 jobs).
```

Notes:

- Added a local `Nat.Partition.count` because this Mathlib version has `Fintype (Nat.Partition n)` but no named count function.
- Defined `positiveSizeClass` and `intPartClass = MSET(positiveSizeClass)`.
- Proved `intPartition_ogf_coeff`.
- Added finite `native_decide` checks for odd-parts equals distinct-parts for `n = 0..10`.
- Added finite Euler pentagonal recurrence checks for `n = 1..10`.
- Added sanity values `p(0)..p(10) = 1,1,2,3,5,7,11,15,22,30,42`.
