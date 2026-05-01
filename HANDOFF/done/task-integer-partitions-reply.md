Done.

- Added `AnalyticCombinatorics/Examples/IntegerPartitions.lean`.
- Used Mathlib's `Nat.Partition n` from `Mathlib.Combinatorics.Enumerative.Partition.Basic`.
- Defined `intPartitionClass` with objects `Σ n, Nat.Partition n` and size equal to the index `n`.
- Proved finite levels and `intPartitionClass.count n = Fintype.card (Nat.Partition n)`.
- Added sanity examples for `n = 0..6`: `1, 1, 2, 3, 5, 7, 11`.
- Added the TODO comment for the F&S OGF product identity.
- Added the new example import to `AnalyticCombinatorics.lean`.

Verification:

- `lake env lean AnalyticCombinatorics/Examples/IntegerPartitions.lean`
- `lake build`

Both passed.
