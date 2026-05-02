Done.

- Extended `AnalyticCombinatorics/Examples/CompositionsEven.lean` sanity checks through `n = 28`.
- Added recurrence-shaped private lemmas and examples for:
  - `evenCompClass.count 23 = 0`
  - `evenCompClass.count 24 = 2048`
  - `evenCompClass.count 25 = 0`
  - `evenCompClass.count 26 = 4096`
  - `evenCompClass.count 27 = 0`
  - `evenCompClass.count 28 = 8192`
- `native_decide` did not time out for the new entries.

Verification:

- `lake build AnalyticCombinatorics.Examples.CompositionsEven` passes.
- Full `lake build` is currently blocked by an existing modified `AnalyticCombinatorics/Examples/SetPartitions.lean` check:
  `Nat.bell 23 = 44583569526191395` evaluates false at line 961.
