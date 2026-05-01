已完成。

- 在 `AnalyticCombinatorics/PartA/Ch1/CombinatorialClass.lean` 的 `end CombinatorialClass` 前加入两个 requested `example`。
- `lake env lean AnalyticCombinatorics/PartA/Ch1/CombinatorialClass.lean` 通过。
- `lake build` 通过；输出只有既有 lint warnings。
- 目标文件 `rg -n "sorry"` 无结果，没有新增 `sorry`。
