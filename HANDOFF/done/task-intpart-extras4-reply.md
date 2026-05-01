Done with caveat.

- Added the `p_21 = 792` sanity check using the existing
  `intPartitionClass_count_eq_card + native_decide` pattern.
- Tried the same checks for `p_22 = 1002`, `p_23 = 1255`,
  `p_24 = 1575`, and `p_25 = 1958`; with Mathlib's default
  `Nat.Partition` `Fintype`, the file did not finish checking in
  reasonable time.
- Documented the local `native_decide` threshold in the Lean file as
  `n = 21`.

Verification:

```text
lake env lean AnalyticCombinatorics/Examples/IntegerPartitions.lean
```

passed.
