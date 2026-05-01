Done.

- Added `compFirstPart : Parameter compositionClass`, returning the first part and `0` on the empty composition.
- Added small bivariate sanity examples for `(n, k)` through `n = 4`, using the existing finite level lemmas and `decide`.
- Added the generic image-sum sanity identity via `CombinatorialClass.jointCount_sum_eq_count`.

Verification:

- `lake env lean AnalyticCombinatorics/Examples/Compositions.lean`
- `lake build`
