Done.

- Appended `labelPow_permClass_count_multichoose`:
  `(CombinatorialClass.labelPow permClass k).count n = n.factorial * Nat.multichoose k n`
- Appended binomial form `labelPow_permClass_count`:
  `(CombinatorialClass.labelPow permClass k).count n = n.factorial * (n + k - 1).choose n`
- Added sanity examples for `k = 0`, `k = 1`, and `k = 2`.
- No new `sorry`s.

Verification:

- `lake env lean AnalyticCombinatorics/PartA/Ch2/LabelledClass.lean`
- `lake build`
