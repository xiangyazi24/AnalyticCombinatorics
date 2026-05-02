Implemented `AnalyticCombinatorics/PartA/Ch1/LatticePaths.lean`.

What is included:
- `Step` with `U` and `D`.
- Computable Dyck predicate `isDyckPath` using prefix nonnegativity and final height zero.
- Bundled `DyckPath` objects with semilength and path length proof.
- `dyckPathClass : CombinatorialClass`.
- Explicit finite enumeration `DyckPath.ofSize`.
- Sanity counts for semilengths `0..4`: `1, 1, 2, 5, 14`.
- Catalan formula checks for `n = 0..4`.
- Binary-tree count equality checks for `n = 0..4`.

The full reflection-principle/Catalan formula and full first-return bijection are not proved; the file records these intended general statements as `Prop` definitions without axioms or `sorry`.

Verification:
- `lake build AnalyticCombinatorics.PartA.Ch1.LatticePaths` passed.
