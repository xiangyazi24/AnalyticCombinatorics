完成。

- 对当前 `lake build` 暴露的 cosmetic linter warnings 做了清理：
  - `linter.style.show`
  - `linter.flexible`（只在具体 declaration/example 上关闭，避免 unscoped option warning）
  - `linter.style.nativeDecide`
  - `linter.style.multiGoal`
- 修改文件：
  - `AnalyticCombinatorics/PartA/Ch1/CombinatorialClass.lean`
  - `AnalyticCombinatorics/PartA/Ch1/Sequences.lean`
  - `AnalyticCombinatorics/PartA/Ch2/LabelledClass.lean`
  - `AnalyticCombinatorics/Examples/BinaryTrees.lean`
  - `AnalyticCombinatorics/Examples/Strings.lean`
  - `AnalyticCombinatorics/Examples/Compositions.lean`
- 未新增 `sorry`，未做语义性证明改写。
- 验证：
  - `lake build` 通过，最终输出无 warnings。
  - `git diff --check` 通过。
