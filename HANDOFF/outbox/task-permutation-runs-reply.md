Done.

- Created `AnalyticCombinatorics/PartA/Ch3/PermutationRuns.lean`.
- Added computable descent/ascent/run count wrappers around the existing Eulerian table.
- Added `totalExcedances`, `subfactorial`, `fixedPointPerms`, row sums, weighted row sums, and `totalFixedPoints`.
- Verified subfactorial values `D_0..D_6`, fixed-point distribution row sums for `n = 0..6`, and mean fixed-point checks for `n = 1..6` with `native_decide`.
- Added the new module to `AnalyticCombinatorics.lean`.
- Verified with:
  `lake build AnalyticCombinatorics.PartA.Ch3.PermutationRuns`
  `lake build AnalyticCombinatorics`
