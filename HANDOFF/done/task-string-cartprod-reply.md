Done.

- Added sanity examples for `(stringClass.cartProd stringClass).count n` at `n = 0..5` in `AnalyticCombinatorics/Examples/Strings.lean`.
- Each example rewrites with `CombinatorialClass.cartProd_count` and discharges with `norm_num [Finset.antidiagonal, stringClass_count_eq_pow]`.
- Verified with `lake env lean AnalyticCombinatorics/Examples/Strings.lean`.
- Verified full build with `lake build`.
