Done.

Modified `AnalyticCombinatorics/Examples/MotzkinTrees.lean` to extend Motzkin count sanity checks through `n = 24`:

- `M(19) = 18199284`
- `M(20) = 50852019`
- `M(21) = 142547559`
- `M(22) = 400763223`
- `M(23) = 1129760415`
- `M(24) = 3192727797`

Each new check uses the existing `count_succ_succ` recurrence proof path, expands the finite antidiagonal sum, rewrites prior count lemmas, then closes by `decide`.

Verification:

- `lake env lean AnalyticCombinatorics/Examples/MotzkinTrees.lean`
- `lake build AnalyticCombinatorics.Examples.MotzkinTrees`
- `lake build`
