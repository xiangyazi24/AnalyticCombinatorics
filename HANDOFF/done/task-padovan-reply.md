Implemented the Padovan compositions example.

- Added `AnalyticCombinatorics/Examples/Padovan.lean`.
- Defined `step23Class` as `(atomOfSize 2).disjSum (atomOfSize 3)`.
- Defined `padovanClass = seqClass step23Class step23Class_count_zero`.
- Added sanity examples for counts `0..10`: `1, 0, 1, 1, 1, 2, 2, 3, 4, 5, 7`.
- Proved the OGF identity:
  `ogfZ padovanClass * (1 - PowerSeries.X ^ 2 - PowerSeries.X ^ 3) = 1`.
- Imported the new example from `AnalyticCombinatorics.lean`.

Verification:

- `lake env lean AnalyticCombinatorics/Examples/Padovan.lean`
- `lake build`

Both pass. No new `sorry`/`admit`.
