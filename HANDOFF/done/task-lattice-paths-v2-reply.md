Done.

- Added `AnalyticCombinatorics/PartA/Ch1/LatticePaths.lean`.
- Defined `dyckCount n := Nat.centralBinom n / (n + 1)`.
- Proved sanity checks for `n = 0..4`.
- Proved `dyckCount_eq_binaryTree_count` for all `n ≤ 6`, with explicit examples for `0..6`.
- Verified with:

```bash
lake build AnalyticCombinatorics.PartA.Ch1.LatticePaths
```

Result: build completed successfully.
