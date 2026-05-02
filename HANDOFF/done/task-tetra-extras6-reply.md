Done.

- Extended `tetraClass.count` sanity checks through `n = 28`.
- Added values:
  - `T_26 = 14564533`
  - `T_27 = 28074040`
  - `T_28 = 54114452`
- No new `sorry`s or axioms.

Verification:

- `lake env lean AnalyticCombinatorics/Examples/Tetranacci.lean`
- `lake build AnalyticCombinatorics.Examples.Tetranacci`
