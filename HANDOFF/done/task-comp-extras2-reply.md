Done.

- Extended `compositionClass.count` sanity checks through `n = 15`.
- Extended `compositionGe2Class.count` sanity checks through `n = 12`.
- Used `rw [...]; decide`; no `native_decide` timeout threshold was hit.
- No new `sorry`s.

Verification:

- `lake env lean AnalyticCombinatorics/Examples/Compositions.lean` passed.
- `lake build AnalyticCombinatorics.Examples.Compositions` passed.

Note: full `lake build` is currently blocked by an unrelated existing failure in `AnalyticCombinatorics/Examples/SetPartitions.lean:961`, where `native_decide` evaluates `Nat.bell 23 = 44583569526191395` as false. This task only modified `Compositions.lean` plus this required reply file.
