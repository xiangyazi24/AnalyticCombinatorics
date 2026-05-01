Done.

- Added derangement sanity examples for `D_13`, `D_14`, and `D_15` in `AnalyticCombinatorics/Examples/Derangements.lean`.
- Kept the existing `rw [derangementClass_count_eq_numDerangements]` + `decide` pattern; no `native_decide` needed.
- Verified with:
  - `lake env lean AnalyticCombinatorics/Examples/Derangements.lean`
  - `lake build`

No new `sorry`s.
