Done.

- Added `largeSchroderNumber` sanity rows for `n = 16, 17, 18`:
  - `20927156706`
  - `111818026018`
  - `600318853926`
- Kept the existing `by decide` style; no `native_decide` threshold needed.
- Verification:
  - `lake env lean AnalyticCombinatorics/Examples/SchroderTrees.lean`
  - `lake build AnalyticCombinatorics.Examples.SchroderTrees`

