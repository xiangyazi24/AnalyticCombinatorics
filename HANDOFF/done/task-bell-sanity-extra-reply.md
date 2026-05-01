Done.

Changed `AnalyticCombinatorics/Examples/SetPartitions.lean` by appending Bell sanity checks for 5, 6, and 7. I used small private Bell-value lemmas plus `norm_num` instead of `native_decide`, so the added checks do not introduce the `native_decide` linter warning.

Verification:
- `lake env lean AnalyticCombinatorics/Examples/SetPartitions.lean`
- `lake build`

Both passed. Existing build warnings remain in other files.
