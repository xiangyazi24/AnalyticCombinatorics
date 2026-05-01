Done.

- Extended `AnalyticCombinatorics/Examples/CompositionsEven.lean` sanity checks through `n = 28`:
  `23 -> 0`, `24 -> 2048`, `25 -> 0`, `26 -> 4096`, `27 -> 0`, `28 -> 8192`.
- Added no `sorry`/`admit`/`axiom` in the file.
- Verified:
  - `lake env lean AnalyticCombinatorics/Examples/CompositionsEven.lean`
  - `lake build AnalyticCombinatorics.Examples.CompositionsEven`

Note: full `lake build` still fails in existing unrelated `AnalyticCombinatorics/Examples/SchroderTrees.lean`
at the `largeSchroderNumber 16/17` native sanity checks.
