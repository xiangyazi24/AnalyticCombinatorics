完成。

- 在 `AnalyticCombinatorics/PartA/Ch2/LabelledClass.lean` 加了 `labelCycCount Atom` 的 sanity examples：0, 1, 2, 3, 4。
- 同时证明了一般定理：
  `labelCycCount_Atom_succ (n : ℕ) : labelCycCount Atom (n + 1) = (n.factorial : ℚ)`。
- 没有新增 `sorry`。
- 已验证：
  - `lake env lean AnalyticCombinatorics/PartA/Ch2/LabelledClass.lean`
  - `lake build`

`lake build` 成功；只剩仓库既有 linter warnings。
