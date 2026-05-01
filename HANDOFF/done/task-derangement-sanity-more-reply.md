完成。

- 已在 `AnalyticCombinatorics/Examples/Derangements.lean` 追加 `count 7 = 1854` 和 `count 8 = 14833` sanity examples。
- 两个例子都用 `decide`，不需要 `native_decide`。
- 已验证：
  - `lake env lean AnalyticCombinatorics/Examples/Derangements.lean`
  - `lake build`

`lake build` 成功；输出中只有既有文件的 lint warnings，没有新错误。
