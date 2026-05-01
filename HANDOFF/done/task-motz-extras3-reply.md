Done.

- Extended Motzkin count sanity through size 18 in `AnalyticCombinatorics/Examples/MotzkinTrees.lean`.
- Added counts:
  - `count 16 = 853467`
  - `count 17 = 2356779`
  - `count 18 = 6536382`
- Kept existing `decide` pattern; no `native_decide` needed.
- Verified with `lake env lean AnalyticCombinatorics/Examples/MotzkinTrees.lean`.
- Verified full build with `lake build`.
