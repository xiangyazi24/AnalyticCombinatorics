Done.

- Added the two BinTree EGF sanity examples to `AnalyticCombinatorics/Examples/BinaryTrees.lean`.
- Adjusted the size-2 proof to rewrite through `BinTree.catalan 2` and `_root_.catalan_two`.
- Verified:
  - `lake env lean AnalyticCombinatorics/Examples/BinaryTrees.lean`
  - `lake build`
- No `sorry`/`admit` in `BinaryTrees.lean`.
