Done.

- Added project-facing theorem `stirlingSecond_succ` in `AnalyticCombinatorics/Examples/SetPartitions.lean`.
- It exposes Mathlib's existing `Nat.stirlingSecond_succ_succ`; no reproving, no axioms, no new `sorry`.
- Verified with:
  - `lake env lean AnalyticCombinatorics/Examples/SetPartitions.lean`
  - `lake build`
