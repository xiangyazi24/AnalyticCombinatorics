Done.

- Added derangement sanity checks through `D_21` in `AnalyticCombinatorics/Examples/Derangements.lean`.
- Used `derangementClass_count_eq_numDerangements` followed by `decide`.
- Verified:
  - `lake env lean AnalyticCombinatorics/Examples/Derangements.lean`
  - `lake build AnalyticCombinatorics.Examples.Derangements`
  - `lake build`
