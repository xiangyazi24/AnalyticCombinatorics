Done.

- Extended `compositionClass.count` sanity checks through `n = 18`.
- Extended `compositionGe2Class.count` sanity checks through `n = 18`.
- No new `sorry`s in `AnalyticCombinatorics/Examples/Compositions.lean`.

Verification:

- `lake env lean AnalyticCombinatorics/Examples/Compositions.lean` passes.
- `lake build` does not pass because of existing unrelated failures in `AnalyticCombinatorics/Examples/Derangements.lean`:
  - line 194: `Nat.numDerangements 25 = 9227046511766524160` is false
  - line 198: `Nat.numDerangements 26 = 239902115640599345920` is false
  - line 202: `Nat.numDerangements 27 = 6474957122295580339200` is false
  - `AnalyticCombinatorics.Examples.Compositions` itself built successfully during `lake build`.
