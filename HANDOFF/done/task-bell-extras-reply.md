已追加 `B_16..B_18` sanity checks 到 `AnalyticCombinatorics/Examples/SetPartitions.lean`，全部使用同一模式：

```lean
rw [labelSetCount_posIntClass_eq_bell]
native_decide
```

结果：
- `B_16 = 10480142147`
- `B_17 = 82864869804`
- `B_18 = 682076806159`

`native_decide` 没有在 `B_18` choke。验证：

```text
lake env lean AnalyticCombinatorics/Examples/SetPartitions.lean
# passed, about 8.8s wall

lake build
# Build completed successfully (2791 jobs), about 6.3s wall

rg -n "sorry|admit" AnalyticCombinatorics/Examples/SetPartitions.lean
# no matches
```
