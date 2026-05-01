已在 `AnalyticCombinatorics/Examples/SetPartitions.lean` 追加 `B_12..B_15` sanity examples，全部经
`labelSetCount_posIntClass_eq_bell` 转到 `Nat.bell`，再用 `native_decide` 验证：

- `B_12 = 4213597`
- `B_13 = 27644437`
- `B_14 = 190899322`
- `B_15 = 1382958545`

`decide` 在这些桥接后的 `ℚ` 等式上从 `n = 12` 起规约卡住，不是 30 秒超时；`native_decide` 的目标文件检查约 4 秒，全仓 `lake build` 通过，约 7 秒。
