Done.

- Added Motzkin count sanity checks through size 21 in `AnalyticCombinatorics/Examples/MotzkinTrees.lean`.
- Verified:
  - `lake env lean AnalyticCombinatorics/Examples/MotzkinTrees.lean`
  - `lake build AnalyticCombinatorics.Examples.MotzkinTrees`
  - `rg -n "sorry" AnalyticCombinatorics/Examples/MotzkinTrees.lean` has no matches.
