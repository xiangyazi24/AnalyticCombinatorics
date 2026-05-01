已完成。

- 新增 `AnalyticCombinatorics/Examples/DyckPaths.lean`。
- 使用 Mathlib 的 `DyckWord` 作为 `DyckPath` 表示，`dyckPathClass` 按 `semilength` 计 size。
- 证明 `dyckPathClass_count : dyckPathClass.count n = _root_.catalan n`。
- 添加 `n = 0..5` sanity checks。由于 `CombinatorialClass.count` 是 `noncomputable`，checks 先 `rw [dyckPathClass_count]` 化到 Mathlib 的 `catalan`，再用 `native_decide`。
- 添加 OGF quadratic TODO comment: `D(z) = 1 + z * D(z)^2`。
- 已加入 `AnalyticCombinatorics.lean` 顶层 imports。

验证：

```bash
lake env lean AnalyticCombinatorics/Examples/DyckPaths.lean
rg -n "sorry|admit" AnalyticCombinatorics/Examples/DyckPaths.lean
lake build
```

结果：Lean 单文件检查通过，`rg` 无匹配，`lake build` 通过。
