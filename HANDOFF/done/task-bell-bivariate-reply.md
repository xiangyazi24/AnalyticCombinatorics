Done.

- Added the Bell 11 sanity dump example in `AnalyticCombinatorics/Examples/SetPartitions.lean`.
- Used the established `labelSetCount_posIntClass_eq_bell` bridge.
- Avoided `native_decide` by adding a small `Nat.bell 11` sanity lemma from the existing Bell sanity lemmas.
- Verified with `lake env lean AnalyticCombinatorics/Examples/SetPartitions.lean`.
- Verified with `lake build`.
