Done.

- Added `AnalyticCombinatorics/PartA/Ch1/UnlabelledStructures.lean`.
- Formalized `necklaceCountTimesN` and `necklaceCount` for binary necklaces using the Burnside/Pólya divisor-sum formula.
- Added `native_decide` checks for `necklaceCount 0..8`, exact numerator quotient checks for `1..8`, and divisibility checks for `1..8`.
- Added a small `unrootedTreeCount` table for OEIS A000055 initial values with sanity checks.

Verification:

```text
lake build AnalyticCombinatorics.PartA.Ch1.UnlabelledStructures
✔ [3285/3285] Built AnalyticCombinatorics.PartA.Ch1.UnlabelledStructures (33s)
Build completed successfully (3285 jobs).
```
