Done.

- Added `permClass_labelProd_Atom_egf` in `AnalyticCombinatorics/PartA/Ch2/LabelledClass.lean`.
- Added the constant-term example for `permClass.egf`.
- Fixed an existing build blocker in `AnalyticCombinatorics/Examples/Derangements.lean` by making the cardinality bridge to Mathlib's `derangements` subtype explicit.
- Verified:
  - `lake env lean AnalyticCombinatorics/PartA/Ch2/LabelledClass.lean`
  - `lake env lean AnalyticCombinatorics/Examples/Derangements.lean`
  - `lake build`
