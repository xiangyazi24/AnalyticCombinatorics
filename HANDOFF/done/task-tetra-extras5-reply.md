Done.

- Extended `tetraClass.count` sanity checks through `n = 25`.
- Added values:
  - `T_23 = 2033628`
  - `T_24 = 3919944`
  - `T_25 = 7555935`
- No new `sorry`s.

Verification:

- `lake env lean AnalyticCombinatorics/Examples/Tetranacci.lean`
- `lake build AnalyticCombinatorics.Examples.Tetranacci`
