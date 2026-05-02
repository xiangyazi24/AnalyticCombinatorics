Done.

Changed `AnalyticCombinatorics/Examples/Surjections.lean`:
- Added `surjectionClass.count` sanity checks for n = 24, 25, 26.
- Kept the requested proof shape: `rw [surjectionClass_count_eq_fubini]; native_decide`.
- Added a local executable wrapper for Stirling numbers so these high-index `native_decide` checks compile quickly while remaining definitionally backed by `Nat.stirlingSecond`.

Verified:
- `lake env lean AnalyticCombinatorics/Examples/Surjections.lean`
- `lake build AnalyticCombinatorics.Examples.Surjections`
