Status: done.

- Added `BinTree.ogfZ_functional_equation`.
- Added `BinTree.ogfZ_quadratic`.
- Added required imports for `ogfZ` and `linear_combination`.

Verification:

- `lake env lean AnalyticCombinatorics/Examples/BinaryTrees.lean`
- `lake build`
- `rg -n "sorry|admit" AnalyticCombinatorics/Examples/BinaryTrees.lean` returned no matches.
