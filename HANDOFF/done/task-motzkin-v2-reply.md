已创建 `AnalyticCombinatorics/PartA/Ch1/MotzkinTrees.lean`。

包含：
- `MotzkinTree` 与 node-count `size`
- `motzkinTreeClass : CombinatorialClass`
- `motzkinTree_count_one` 到 `motzkinTree_count_five`
- `motzkinTree_ogf_eq :
  motzkinTreeClass.ogf =
    PowerSeries.X * (1 + motzkinTreeClass.ogf + motzkinTreeClass.ogf ^ 2)`

已验证：

```bash
lake build AnalyticCombinatorics.PartA.Ch1.MotzkinTrees
```

结果：通过。
