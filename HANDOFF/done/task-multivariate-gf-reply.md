Done.

- Created `AnalyticCombinatorics/PartA/Ch3/MultivariateGF.lean`.
- Added finite `bgf` worked examples using a two-object size-1 class with marker values `0` and `1`.
- Added recursive `eulerianNumber`, recurrence/boundary/out-of-range lemmas, row-sum checker, and row-symmetry checker.
- Verified Eulerian table values, row sums for `n = 0..7`, and symmetry for `n = 1..6` with `native_decide`.
- Verified with:
  `lake build AnalyticCombinatorics.PartA.Ch3.MultivariateGF`
