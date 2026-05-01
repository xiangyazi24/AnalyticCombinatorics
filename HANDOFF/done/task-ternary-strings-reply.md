完成。

- 在 `AnalyticCombinatorics/Examples/Strings.lean` 末尾追加了 `ternaryClass : CombinatorialClass`，对象为 `Fin 3`，所有对象 size 为 1。
- 添加了 `DecidableEq` / `Fintype` bridge instances。
- 添加了 `ternaryClass.count_zero`、`ternaryClass.count_one`、非 1 层为空的私有引理。
- 添加了 `ternaryStringClass := seqClass ternaryClass ternaryClass.count_zero`。
- 证明了 `ternaryStringClass_count_eq_pow (n) : ternaryStringClass.count n = 3 ^ n`，沿用 binary string 的递推模式。
- 添加了 `n = 0..6` sanity examples：`1, 3, 9, 27, 81, 243, 729`。

验证：

```bash
lake env lean AnalyticCombinatorics/Examples/Strings.lean
lake build
rg -n "sorry" AnalyticCombinatorics/Examples/Strings.lean
```

`lake build` 通过；未新增 `sorry`。
