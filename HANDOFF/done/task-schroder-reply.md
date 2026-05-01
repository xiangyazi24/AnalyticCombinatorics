Done.

Files changed:
- `AnalyticCombinatorics/Examples/SchroderTrees.lean`
- `AnalyticCombinatorics.lean`

Notes:
- Added filtered raw syntax for `SchroderTree`, because the dependent `List` constructor with a proof argument runs into Lean nested-inductive awkwardness.
- `SchroderTree.asClass` uses the standard finite size `leaves - 1`.
- Added `largeSchroderNumber` with checked examples:
  `1, 2, 6, 22, 90, 394`.
- No new `sorry`.

Verification:
- `lake env lean AnalyticCombinatorics/Examples/SchroderTrees.lean`
- `lake build`
