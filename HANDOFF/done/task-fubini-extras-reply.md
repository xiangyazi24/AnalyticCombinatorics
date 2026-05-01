Done.

- Added Fubini sanity examples for n = 4, 5, 6 in `AnalyticCombinatorics/Examples/SetPartitions.lean`.
- Used `decide`; no `native_decide` or extra computation chain was needed.
- Verified:
  - `lake env lean AnalyticCombinatorics/Examples/SetPartitions.lean`
  - `lake build`

`lake build` completes successfully. Existing linter warnings remain in unrelated files.
