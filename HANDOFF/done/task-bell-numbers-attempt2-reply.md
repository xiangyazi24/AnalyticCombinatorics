done

Diff summary:
- Added `AnalyticCombinatorics/Examples/SetPartitions.lean`.
- Proved `labelSetCount_posIntClass_eq_bell`.
- Added the new example module to `AnalyticCombinatorics.lean`.

Proof route:
- Defined `labelSetSeries`, `labelSetPartial`, and `bellSeries`.
- Proved `posIntClass.egf' = exp`.
- Proved `labelSetSeries posIntClass` and `bellSeries` satisfy the same coefficient recurrence via
  `F' = exp * F`.
- Used strong induction on coefficients, then cleared factorial denominators.

Verification:
- `lake build AnalyticCombinatorics.Examples.SetPartitions` passes.
- `lake build` passes.

Codex: idle — task done
