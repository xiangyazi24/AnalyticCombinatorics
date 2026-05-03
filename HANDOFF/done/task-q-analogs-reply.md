Done.

Created `AnalyticCombinatorics/PartA/Ch1/QAnalogs.lean`.

Contents:
- `qNumber` and `qFactorial` as natural-number evaluations.
- `gaussianBinomial` by the Pascal recurrence
  `[n+1 choose k+1]_q = [n choose k]_q + q^(k+1) * [n choose k+1]_q`.
- Boundary lemmas for the recurrence.
- q=2 sanity checks:
  `[3 choose 1]_2 = 7`, `[4 choose 2]_2 = 35`, `[5 choose 2]_2 = 155`.
- Small Pascal-identity checks at q=2.
- `gaussianRowSum` with q=2 checks for rows `0..5`.

Verification:
- `lake build AnalyticCombinatorics.PartA.Ch1.QAnalogs`
- Result: success.

Note:
- I also tried `lake build AnalyticCombinatorics`; it fails before reaching this new module because the existing root import set already has a duplicate `necklaceCount` name from `UnlabelledStructures` and `Necklaces`.
