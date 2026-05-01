Done.

- Added `AnalyticCombinatorics/Examples/Derangements.lean`.
- Defined `derangementClass` as fixed-point-free permutations of `Fin n`.
- Proved `derangementClass_count_eq_numDerangements`.
- Added the root import in `AnalyticCombinatorics.lean`.

Verification:

- `lake env lean AnalyticCombinatorics/Examples/Derangements.lean`
- `lake build`

Note: this Mathlib version exposes the counting sequence as top-level `numDerangements`, not `Nat.numDerangements`; the example file adds a namespace bridge `Nat.numDerangements` for the requested statement.
