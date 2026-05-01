Done.

- Added plane tree sanity checks:
  - `planeTreeClass.count 5 = 42`
  - `planeTreeClass.count 6 = 132`
- Used `norm_num` after `planeTreeClass_count`; `decide` could not reduce `_root_.catalan 5/6`, and `native_decide` passed but introduced style warnings.
- Verified with `lake build`.
- No new `sorry`/`admit` in `AnalyticCombinatorics/Examples/PlaneTrees.lean`.
