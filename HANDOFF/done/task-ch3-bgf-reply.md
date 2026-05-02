Implemented.

Files changed:
- `AnalyticCombinatorics/PartA/Ch3/Parameters.lean`
- `AnalyticCombinatorics/PartA/Ch2/LabelledClass.lean`

Added in `Parameters.lean`:
- `CombinatorialClass.bgf`
- `CombinatorialClass.coeff_bgf`
- `CombinatorialClass.bgf_eval_one`
- `CombinatorialClass.cumulatedCost`
- `CombinatorialClass.cumulatedCost_eq_sum_param`
- `CombinatorialClass.meanParam`
- `CombinatorialClass.meanParam_eq_cumulatedCost_div`

Note: `bgf_eval_one` uses `Polynomial.evalRingHom 1`, since `PowerSeries.map` expects a ring hom.

Added downstream permutation sanity support in `LabelledClass.lean`:
- `permClass.jointCount_numFixedPoints_eq_card_filter`
- `permClass.cumulatedCost_numFixedPoints_eq_sum_univ`
- native-decide sanity examples:
  - `jointCount 2 0 = 1`
  - `jointCount 2 2 = 1`
  - `jointCount 3 0 = 2`
  - `jointCount 3 1 = 3`
  - `jointCount 3 3 = 1`
  - `cumulatedCost 3 = 6`
  - `meanParam 3 = 1`

Verification:
- `lake build AnalyticCombinatorics.PartA.Ch3.Parameters`
- `lake build AnalyticCombinatorics.PartA.Ch2.LabelledClass`
