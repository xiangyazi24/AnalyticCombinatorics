Done.

Created `AnalyticCombinatorics/PartA/Ch1/SchroederTheory.lean` with:

- `schroederCount : ℕ → ℕ`
- sanity checks for `1, 2, 6, 22, 90`
- coefficient recursion matching `S = 1 + z*S + z*S^2`
- `schroederOGF : PowerSeries ℕ`
- proof of the quadratic OGF equation

Verified:

```bash
lake build AnalyticCombinatorics.PartA.Ch1.SchroederTheory
```

Result: build succeeded. No `sorry` or `axiom` in the new file.
