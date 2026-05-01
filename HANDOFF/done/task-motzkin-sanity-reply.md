DONE

- Updated `MotzTree.size` to count edges, so binary nodes contribute `2`; this gives OEIS A001006 rather than the large Schroeder recurrence.
- Added `MotzTree.count_one` and replaced the recurrence with `MotzTree.count_succ_succ`.
- Added sanity examples for `MotzTree.asClass.count 0..6 = 1, 1, 2, 4, 9, 21, 51`.
- Updated the OGF equation to `M = 1 + X * M + X * (X * M^2)`.

Verification:

- `lake env lean AnalyticCombinatorics/Examples/MotzkinTrees.lean`
- `lake build`
