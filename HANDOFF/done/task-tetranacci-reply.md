Done.

- Added `AnalyticCombinatorics/Examples/Tetranacci.lean`.
- Defined `step1234Class` and `tetraClass`.
- Proved sanity examples for `tetraClass.count 0..8 = 1, 1, 2, 4, 8, 15, 29, 56, 108`.
- Proved the OGF identity:
  `ogfZ tetraClass * (1 - X - X^2 - X^3 - X^4) = 1`.
- Added the new example to `AnalyticCombinatorics.lean`.

Verification:

- `lake env lean AnalyticCombinatorics/Examples/Tetranacci.lean`
- `lake build`

Both passed. No new `sorry`s in the new file.
