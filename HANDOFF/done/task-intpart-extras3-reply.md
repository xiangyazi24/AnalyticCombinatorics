已完成。

- 在 `AnalyticCombinatorics/Examples/IntegerPartitions.lean` 追加了 `p_16` 到 `p_20` 的 sanity examples。
- 全部使用现有 `intPartitionClass_count_eq_card` + `native_decide` 模式。
- `native_decide` 到 `n = 20` 可通过，没有需要记录的失败阈值。
- 验证：`lake env lean AnalyticCombinatorics/Examples/IntegerPartitions.lean` 通过；`lake build` 通过。
