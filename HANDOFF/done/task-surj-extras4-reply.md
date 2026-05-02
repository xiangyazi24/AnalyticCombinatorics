Done.

- Appended `surjectionClass.count` sanity checks for `n = 16` and `n = 17`.
- Both use `surjectionClass_count_eq_fubini` followed by `native_decide`.
- `lake env lean AnalyticCombinatorics/Examples/Surjections.lean` passes.
- `lake build` passes.
- `native_decide` did not blow up through `n = 17`, so no threshold was documented.
