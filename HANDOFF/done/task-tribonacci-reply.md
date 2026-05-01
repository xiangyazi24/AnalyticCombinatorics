Done.

- Added `AnalyticCombinatorics/Examples/Tribonacci.lean`.
- Defined `step123Class` and `tribClass`.
- Added sanity examples for `tribClass.count 0..7 = 1, 1, 2, 4, 7, 13, 24, 44` using `decide` on numeric checks.
- Added the OGF identity:
  `ogfZ tribClass * (1 - X - X^2 - X^3) = 1`.
- Imported the new example from `AnalyticCombinatorics.lean`.

Verification:

```text
lake build
Build completed successfully (2785 jobs).
```
