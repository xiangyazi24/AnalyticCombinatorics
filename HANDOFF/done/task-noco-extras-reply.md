Done.

- Appended sanity checks for `noConsecOnesClass.count` at `n = 7..11`.
- Each new check uses `noConsecOnesClass_count_eq_fib` followed by `decide`.
- Verified with:
  - `lake env lean AnalyticCombinatorics/Examples/StringsNoConsecutiveOnes.lean`
  - `lake build`
