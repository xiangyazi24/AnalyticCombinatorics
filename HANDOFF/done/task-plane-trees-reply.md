Done.

Created `AnalyticCombinatorics/PartA/Ch1/PlaneTrees.lean`.

Proved:
- `PlaneTree` with recursive node-counting size.
- `planeTreeClass : CombinatorialClass`, including `finite_level`.
- `planeTree_count_zero`.
- `planeTree_count_succ_seq`.
- `planeTree_ogf_satisfies`: `T = X * SEQ(T)`.
- `planeTree_ogf_quadratic`: `T = X + T^2`.
- `planeTree_count_recursion`: Catalan convolution for coefficients.
- `planeTree_ogf_eq`: over `ℤ[[z]]`, `(1 - T) * T = X`.
- sanity checks `count 1 = 1`, `count 2 = 1`, `count 3 = 2`, `count 4 = 5`, `count 5 = 14`.

Verification:
- `lake build AnalyticCombinatorics.PartA.Ch1.PlaneTrees` passes.
