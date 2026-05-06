已完成。

- 新增 `AnalyticCombinatorics/PartA/Ch2/RandomMappings.lean`
- 定义 `mappingCount`, `idempotentCount`, `labeledRootedTreeCount`, `labeledTreeCount`
- 用 `native_decide` 检查了 mapping count、idempotent count `n = 0..6`、Cayley rooted/unrooted 数值
- 证明了 `n ≥ 2` 时 `labeledRootedTreeCount n = n * labeledTreeCount n`
- 已验证：

```bash
lake build AnalyticCombinatorics.PartA.Ch2.RandomMappings
```

结果：通过。
