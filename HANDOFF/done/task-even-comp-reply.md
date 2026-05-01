Done.

- Added `AnalyticCombinatorics/Examples/CompositionsEven.lean`.
- Defined `evenPartClass` as the subtype of positive even natural numbers, sized by value.
- Defined `evenCompClass := seqClass evenPartClass evenPartClass.count_zero`.
- Added sanity examples for `n = 0..10` with counts `1, 0, 1, 0, 2, 0, 4, 0, 8, 0, 16`, using `native_decide` after rewriting to concrete arithmetic checks.
- Added the new example import to `AnalyticCombinatorics.lean`.

Verification:

- `lake env lean AnalyticCombinatorics/Examples/CompositionsEven.lean`
- `lake build`

Both pass. No new `sorry`.
