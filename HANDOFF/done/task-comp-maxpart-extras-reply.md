Done.

- Extended `compositionClass.jointCount compMaxPart n k` sanity checks through `n = 6`.
- Added explicit level enumerations for `n = 5, 6`, then reused the existing `rw [CombinatorialClass.jointCount, compositionClass_level_*]` + `decide` pattern.
- New max-part rows:
  - `n = 5`: `1, 7, 5, 2, 1`; sum check `= compositionClass.count 5 = 16`.
  - `n = 6`: `1, 12, 11, 5, 2, 1`; sum check `= compositionClass.count 6 = 32`.
- No new `sorry`s.

Verification:

```text
lake env lean AnalyticCombinatorics/Examples/Compositions.lean
lake build
```

Both pass.

Note: full `lake build` initially failed in the existing modified `AnalyticCombinatorics/Examples/Tribonacci.lean`; I added a computable `DecidableEq tribClass.Obj` instance so that file builds cleanly too.
