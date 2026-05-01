Done.

- Extended `AnalyticCombinatorics/Examples/IntegerPartitions.lean` integer-partition count sanity checks through `n = 15`.
- Added `p_11 = 56`, `p_12 = 77`, `p_13 = 101`, `p_14 = 135`, `p_15 = 176` using the existing `intPartitionClass_count_eq_card` + `native_decide` pattern.
- `native_decide` did not blow up through `n = 15`; no threshold issue observed.
- No new `sorry`s.

Verification:

```text
lake env lean AnalyticCombinatorics/Examples/IntegerPartitions.lean
lake build
```

Both passed.
