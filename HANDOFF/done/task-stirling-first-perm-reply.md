完成。

- 在 `AnalyticCombinatorics/Examples/SetPartitions.lean` 追加了
  `stirlingFirst_sum_eq_factorial`：
  `∑ k ∈ Finset.range (n + 1), Nat.stirlingFirst n k = n.factorial`
- 同时保留了任务里给出的 `example` 形式，直接应用该 theorem。
- Mathlib 当前没有现成的总和 identity；证明使用 `Nat.stirlingFirst_succ_succ` 递推、
  `Nat.stirlingFirst_eq_zero_of_lt` 以及端点 shift lemma。
- 未引入未完成证明占位。

验证：

- `lake build AnalyticCombinatorics.Examples.SetPartitions` 通过。
- `lake build` 通过。
- 构建中出现的 lint warnings 来自既有文件/既有代码路径，不是本次新增 theorem。
