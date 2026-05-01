Done.

- Added derangement sanity checks for D_16, D_17, and D_18 in `AnalyticCombinatorics/Examples/Derangements.lean`.
- Kept the existing `derangementClass_count_eq_numDerangements` + `decide` pattern.
- Verified:
  - `lake env lean AnalyticCombinatorics/Examples/Derangements.lean`
  - `lake build`

Note: after the build, `git status` also showed unrelated modified files:
`AnalyticCombinatorics/Examples/IntegerPartitions.lean` and
`AnalyticCombinatorics/Examples/Tetranacci.lean`. I did not edit or revert them.
