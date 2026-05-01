Done.

- Appended Bell EGF documentation theorems to `AnalyticCombinatorics/Examples/SetPartitions.lean`.
- Added coefficient identities for `bellSeries` and `labelSetSeries posIntClass`.
- Exposed the Bell ODE in `posIntClass.egf = exp(z) - 1` form:
  `B' = (1 + posIntClass.egf) * B`, for both `labelSetSeries posIntClass` and `bellSeries`.
- No blocker: the existing ODEs were already cleanly exposed.

Verification:

- `lake build AnalyticCombinatorics.Examples.SetPartitions`
- `lake build`

Both passed. The build still reports pre-existing lint warnings in other files.
