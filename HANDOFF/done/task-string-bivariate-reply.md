完成。

- 在 `AnalyticCombinatorics/Examples/Strings.lean` 增加了 `stringNumTrue : Parameter stringClass`，复用现有 `numOnes` 的 `List Bool` true-count 定义。
- 增加了指定的 joint count sanity examples：`(3,0)=1`、`(3,1)=3`、`(3,2)=3`、`(3,3)=1`、`(4,2)=6`。
- 增加了总和 identity：
  `∑ k ∈ (stringClass.level 4).image stringNumTrue, stringClass.jointCount stringNumTrue 4 k = 16`，
  由 `CombinatorialClass.jointCount_sum_eq_count` 和 `stringClass_count_eq_pow` 推出。

验证：`lake build` 通过。
