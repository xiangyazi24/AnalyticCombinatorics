Done.

- `fibNumParts` already existed, so I did not redefine it.
- Added Fibonacci joint-count sanity examples for the requested small `(n, k)` values through `n = 5`.
- Added the optional size-5 fiber-sum sanity check, using `jointCount_sum_eq_count`, giving `8`.
- Verification: `lake env lean AnalyticCombinatorics/Examples/Fibonacci.lean` and `lake build` both pass.
