Done.

- Added `compMaxPart : Parameter compositionClass`, using `foldr max 0`; the empty composition therefore has max part `0`.
- Added the requested small `jointCount compMaxPart` sanity examples for `n = 0, 1, 2, 3, 4`, proved with `decide` after rewriting small levels to explicit finite sets.

Verification:

- `lake env lean AnalyticCombinatorics/Examples/Compositions.lean`
- `lake build`
