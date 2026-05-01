Done.

Changed `AnalyticCombinatorics/Examples/Surjections.lean`:
- Extended the Fubini sanity comment through `n = 13`.
- Added sanity examples for `surjectionClass.count 11`, `12`, and `13`.
- Used the existing `rw [surjectionClass_count_eq_fubini]` pattern with `native_decide`, locally disabling the native-decide style linter only for those examples.

Verification:
- `lake env lean AnalyticCombinatorics/Examples/Surjections.lean`
- `lake build AnalyticCombinatorics`
