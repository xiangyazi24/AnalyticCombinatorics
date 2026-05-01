Done.

- Extended `AnalyticCombinatorics/Examples/Tetranacci.lean` sanity counts through `n = 18`.
- Added private count lemmas and examples for:
  - `count 15 = 10671`
  - `count 16 = 20569`
  - `count 17 = 39648`
  - `count 18 = 76424`
- Verification:
  - `lake env lean AnalyticCombinatorics/Examples/Tetranacci.lean`
  - `lake build`
