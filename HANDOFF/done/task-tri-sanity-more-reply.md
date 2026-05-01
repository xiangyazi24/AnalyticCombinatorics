Done.

- Added triangulation sanity examples for `count 7 = 429` and `count 8 = 1430`.
- Used the existing `norm_num [_root_.catalan_eq_centralBinom_div, Nat.centralBinom, Nat.choose]` proof style instead of `native_decide`, avoiding new native-decide warnings.
- Verified:
  - `lake env lean AnalyticCombinatorics/Examples/Triangulations.lean`
  - `lake build`

No new `sorry`s.
