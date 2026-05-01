Done.

- Added triangulation sanity checks for `n = 13, 14, 15` in `AnalyticCombinatorics/Examples/Triangulations.lean`.
- Each uses the existing `triangulationClass_count` bridge plus `norm_num`.
- Verified:
  - `lake env lean AnalyticCombinatorics/Examples/Triangulations.lean`
  - `lake build`

Note: `lake build` succeeds. It reports `native_decide` style warnings in the current worktree's `AnalyticCombinatorics/Examples/PlaneTrees.lean`; that file was not part of this task's edit.
