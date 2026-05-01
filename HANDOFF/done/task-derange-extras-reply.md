Done.

- Confirmed `derangementClass.count n = Nat.numDerangements n` is already established by `derangementClass_count_eq_numDerangements`.
- Added four new explicit small-value sanity examples in `AnalyticCombinatorics/Examples/Derangements.lean`:
  - `D_9 = 133496`
  - `D_10 = 1334961`
  - `D_11 = 14684570`
  - `D_12 = 176214841`
- Used `decide`; no `native_decide` was needed. I briefly tried `native_decide`, but it produced mathlib style-linter warnings, while `decide` was fast.
- No blockers.

Verification:

```text
lake env lean AnalyticCombinatorics/Examples/Derangements.lean
lake build
```

Both passed. `lake build` completed successfully with 2780 jobs.
