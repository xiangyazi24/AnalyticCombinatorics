Done.

- Added complete `stringNumTrue` Pascal rows for `n = 5` and `n = 6` in `AnalyticCombinatorics/Examples/Strings.lean`.
- Used the existing proof pattern: rewrite `stringNumTrue` to `numOnes`, apply `stringClass_jointCount_numOnes`, then `decide`.
- Verified:
  - `lake env lean AnalyticCombinatorics/Examples/Strings.lean`
  - `lake build AnalyticCombinatorics`

No new `sorry`s.
