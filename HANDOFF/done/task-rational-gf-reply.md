Done.

Created `AnalyticCombinatorics/PartB/Ch4/RationalGF.lean` with:

- `geom_coeff` for coefficients of `PowerSeries.mk (fun n => a ^ n)`.
- `isLinearRecurrence` using coefficient lists.
- finite boolean recurrence checks, including Fibonacci through `n = 20` via `native_decide`.
- finite growth-bound checks for a geometric sequence and Fibonacci through `n = 20`.

Verified:

```bash
lake build AnalyticCombinatorics.PartB.Ch4.RationalGF
```

Result: build completed successfully.
