Done.

- Added `largeSchroderNumber` sanity checks through `k = 24`:
  - `largeSchroderNumber 22 = 518431875418926`
  - `largeSchroderNumber 23 = 2832923350929742`
  - `largeSchroderNumber 24 = 15521467648875090`
- Used the existing `by decide` proof shape.
- Verified:
  - `lake env lean AnalyticCombinatorics/Examples/SchroderTrees.lean`
  - `lake build`
