完成。

创建文件：

- `AnalyticCombinatorics/PartA/Ch1/GeneralTrees.lean`

内容包括：

- `taryTreeCount (t n : ℕ) : ℕ`
- 全称整除引理 `taryTreeCount_dvd_choose`
- 无除法的 Fuss-Catalan 公式：
  `(t * n + 1) * taryTreeCount t n = (t * n + 1).choose n`
- 二叉特例匹配 Mathlib Catalan：
  `taryTreeCount_two_eq_catalan`
- 二叉特例匹配本章 `binaryTreeClass.count`：
  `taryTreeCount_two_eq_binaryTreeClass_count`
- t=2 和 t=3 的 `native_decide` sanity checks
- Cayley alias `cayleyTreeCount`
- Cayley cross-reference theorem `cayley_matches_labelled`
- Cayley formula re-export `cayleyTreeCount_formula`

验证：

```text
lake build AnalyticCombinatorics.PartA.Ch1.GeneralTrees
```

结果：

```text
Build completed successfully (3324 jobs).
```
