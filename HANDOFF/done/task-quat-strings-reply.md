Done.

- Appended `quatClass : CombinatorialClass` over `Fin 4`, with all objects of size 1.
- Added `DecidableEq` and `Fintype` bridge instances for `quatClass.Obj`.
- Added `quatStringClass := seqClass quatClass quatClass.count_zero`.
- Proved `quatStringClass_count_eq_pow (n) : quatStringClass.count n = 4 ^ n`.
- Added sanity examples for `n = 0..6`: `1, 4, 16, 64, 256, 1024, 4096`.

Verification:

- `lake env lean AnalyticCombinatorics/Examples/Strings.lean`
- `lake build`

No new `sorry`/`admit`.
