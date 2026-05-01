Done.

- Extended `StringsNoConsecutiveOnes.lean` sanity checks through `n = 15`.
- Used `noConsecOnesClass_count_eq_fib` followed by `decide` for `n = 12..15`.
- Verified with `lake env lean AnalyticCombinatorics/Examples/StringsNoConsecutiveOnes.lean`.
- Verified with `lake build`.

Note: `lake build` completed successfully; it emitted pre-existing `native_decide` linter warnings in `AnalyticCombinatorics/Examples/Surjections.lean`.
