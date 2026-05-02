Implemented additions in `AnalyticCombinatorics/PartB/Ch6/TransferTheorems.lean`.

Added:
- coefficient checks for `(1 - X)⁻¹`, `(1 - X)⁻²`, and `(1 - X)⁻(k+1)` over `ℚ[[X]]`;
- `catalan_formula` for `binaryTreeClass.count n`;
- `centralBinom_formula`;
- `exponentialGrowthRate`, `nthRootSample`, growth-rate proposition statements for Catalan/Motzkin/Fibonacci;
- finite sample growth-window checks;
- `IsDominantSingularity` and `dominantSingularityPrinciple`.

Verification status:
- Fixed the first Lean errors from `lake build AnalyticCombinatorics.PartB.Ch6.TransferTheorems`.
- A subsequent build started rebuilding missing Mathlib oleans from scratch and had not reached `TransferTheorems.lean` again before handoff. I did not claim final build success.
