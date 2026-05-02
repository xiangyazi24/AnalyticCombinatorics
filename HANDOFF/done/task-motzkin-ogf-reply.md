Implemented `AnalyticCombinatorics/PartA/Ch1/MotzkinTrees.lean`.

Contents:
- `MotzkinTree` inductive type with `leaf`, `unary`, `binary`.
- Node-counting `MotzkinTree.size`.
- `motzkinTreeClass : CombinatorialClass`.
- OGF theorem:
  `motzkinTree_ogf_eq :
    motzkinTreeClass.ogf = X * (1 + motzkinTreeClass.ogf + motzkinTreeClass.ogf ^ 2)`.
- Sanity count theorems for sizes `0..5`, including required Motzkin values `1, 1, 2, 4, 9`.

No `sorry` or `axiom` occurs in the new file.

Verification note:
- `rg -n "sorry|axiom" AnalyticCombinatorics/PartA/Ch1/MotzkinTrees.lean` returns no matches.
- `lake build AnalyticCombinatorics.PartA.Ch1.MotzkinTrees` initially exposed Lean proof errors, which were fixed.
- Subsequent verification is currently blocked by a corrupted/missing local Lake build cache: `.lake/build/lib/lean/AnalyticCombinatorics/PartA/Ch1/CombinatorialClass.olean` is missing, and rebuilding dependencies triggered repeated mathlib output-file errors such as missing `Mathlib/.../*.olean` under `.lake/packages/mathlib/.lake/build/lib/lean`.
