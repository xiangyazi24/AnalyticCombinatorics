Done.

Changed `AnalyticCombinatorics/Examples/IntegerPartitions.lean`:
- extended the sanity-check comment through `p_10`;
- added examples for `p_7 = 15`, `p_8 = 22`, `p_9 = 30`, and `p_10 = 42`;
- kept the existing `rw [intPartitionClass_count_eq_card]` + `native_decide` proof style.

Verification:
- `lake env lean AnalyticCombinatorics/Examples/IntegerPartitions.lean`
- `lake build`

Both passed. No new `sorry`s.
