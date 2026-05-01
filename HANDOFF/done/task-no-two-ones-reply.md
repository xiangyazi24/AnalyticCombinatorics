完成。

- 新增 `AnalyticCombinatorics/Examples/StringsNoConsecutiveOnes.lean`。
- 定义了 `noTwoOnes : List Bool → Prop` 及可判定实例。
- 定义了 `NoConsecOnesWord n` 和 `noConsecOnesClass`，大小为长度索引 `n`，并证明 `finite_level`。
- 增加 `noConsecOnesClass.count_eq_card`，把 level 计数桥接到固定长度 restricted words 的 `Fintype.card`。
- 添加 sanity checks：`count 0..6 = 1, 2, 3, 5, 8, 13, 21`，全部用 `decide` 通过。
- 留了 TODO：`noConsecOnesClass.count n = Nat.fib (n + 2)`。
- 已在 `AnalyticCombinatorics.lean` 加 import。

验证：

```text
lake build
Build completed successfully (2788 jobs).
```

无新增 `sorry`。`decide` 能算到 `n = 6`，没有遇到计算阈值问题。
