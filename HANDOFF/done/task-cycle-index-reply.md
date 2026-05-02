Done.

- Created `AnalyticCombinatorics/PartA/Ch2/CycleIndex.lean`.
- Added `cycleTypeCount` with the unsigned Stirling-first recurrence.
- Added native-decide sanity checks for rows 3 and 4, row sums for 1 through 6, checked row sums for 0 through 8, and checked derangement/no-fixed-point counts for 0 through 6.
- Proved `stirling1_row_sum` for all `n`.

Verification:

```text
lake build AnalyticCombinatorics.PartA.Ch2.CycleIndex
✔ [3286/3286] Built AnalyticCombinatorics.PartA.Ch2.CycleIndex (62s)
Build completed successfully (3286 jobs).
```
