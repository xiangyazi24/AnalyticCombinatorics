Done.

- Added `AnalyticCombinatorics/PartA/Ch2/BellNumbers.lean`.
- Defined `bellCount` and `stirling2`.
- Proved the Bell recurrence theorem.
- Added `native_decide` checks for `B(0)` through `B(6)`.
- Added Stirling-sum checks for `n = 0` through `6`, plus a bounded theorem over `n ≤ 6`.
- Imported the new module from `AnalyticCombinatorics.lean`.

Verification:

```text
lake build AnalyticCombinatorics.PartA.Ch2.BellNumbers
✔ Built AnalyticCombinatorics.PartA.Ch2.BellNumbers
```
