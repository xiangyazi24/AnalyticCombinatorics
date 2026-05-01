Done.

- Added `intPartNumParts : Parameter intPartitionClass` using `p.2.parts.card`.
- Added a computable bridge lemma from `jointCount` over `intPartitionClass.level` to the filtered `Finset.univ : Finset (Nat.Partition n)`.
- Added requested bivariate sanity examples for `(4,1)`, `(4,2)`, `(4,3)`, `(4,4)`, `(5,2)`, `(5,3)`.
- Added the optional small sum identity for `n = 4`.

Verification:

- `lake env lean AnalyticCombinatorics/Examples/IntegerPartitions.lean`
- `lake build`
