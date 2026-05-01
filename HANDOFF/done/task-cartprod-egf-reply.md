完成。

- 在 `AnalyticCombinatorics/PartA/Ch1/CombinatorialClass.lean` 中加入了 cartProd 与 labelProdCount 计数差异的两个 `example`。
- 为了让 Ch1 能引用 `labelProdCount`，把 `labelProdCount` 的纯计数定义从 Ch2 上移到 Ch1；Ch2 继续使用同一个定义。
- 没有新增 `sorry`。
- 验证：`lake build` 通过。
