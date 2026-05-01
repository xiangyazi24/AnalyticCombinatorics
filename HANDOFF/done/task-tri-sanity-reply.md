Done.

- Added triangulation sanity checks for counts 0 through 4 in `AnalyticCombinatorics/Examples/Triangulations.lean`.
- Used existing Catalan lemmas for values 0 through 3 and the central-binomial closed form with `norm_num` for value 4, since `decide` does not reduce `_root_.catalan`.
- Verified with `lake env lean AnalyticCombinatorics/Examples/Triangulations.lean`.
- Verified full project with `lake build`.

No new `sorry`s.
