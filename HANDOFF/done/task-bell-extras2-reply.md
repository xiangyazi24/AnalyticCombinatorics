Done.

- Added Bell sanity checks for `B_19 = 5832742205057` and `B_20 = 51724158235372` in `AnalyticCombinatorics/Examples/SetPartitions.lean`.
- Used the existing `labelSetCount_posIntClass_eq_bell` + `native_decide` pattern.
- `native_decide` did not choke through `B_20`; no threshold documented.
- `lake env lean AnalyticCombinatorics/Examples/SetPartitions.lean` passes.
- `lake build AnalyticCombinatorics.Examples.SetPartitions` passes.
- Full `lake build` is blocked outside the requested file by deterministic heartbeat timeouts in `AnalyticCombinatorics/Examples/Tribonacci.lean` around lines 384, 386, 393, and 395.
