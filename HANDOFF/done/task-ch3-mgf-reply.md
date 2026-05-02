Done.

- Wrote `AnalyticCombinatorics/PartA/Ch3/Moments.lean`.
- Defined `CombinatorialClass.secondMomentParam` and `CombinatorialClass.varianceParam`.
- Added binary-tree parameters `binaryTreeLeaves` and `binaryTreePathLength`.
- Verified cumulated leaves for `n = 0..4` by `native_decide`.
- Verified cumulated path length for `n = 0..4` by `native_decide`.
- Added a `native_decide` numeric monotonicity check for average path length per internal node over `n = 1..6`.
- Confirmed the module is imported from `AnalyticCombinatorics.lean`.

Verification:

```text
lake build AnalyticCombinatorics.PartA.Ch3.Moments
✔ Built AnalyticCombinatorics.PartA.Ch3.Moments
Build completed successfully
```

Note: I also started an extra root-module build. The current root file includes other in-progress modules beyond this task; the build only emitted an existing `Ch2/Surjections.lean` lint warning, then ran for too long without further output. The required target build above completed successfully.
