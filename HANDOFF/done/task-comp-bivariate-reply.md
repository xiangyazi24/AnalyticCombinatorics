Done.

- Added the three `compositionClass.jointCount numParts 3 k` sanity examples for `k = 1, 2, 3`.
- Added a local helper for the two-object fiber case, matching the existing one-object helper style.
- No new `sorry`s in `AnalyticCombinatorics/Examples/Compositions.lean`.

Verification:

- `lake env lean AnalyticCombinatorics/Examples/Compositions.lean`
- `lake build`
