完成。

写入：
- `AnalyticCombinatorics/PartA/Ch2/Derangements.lean`

内容：
- `derangeCount : ℕ → ℕ`
- `derangeCount 0..5` sanity theorems, all via `native_decide`
- standalone recurrence theorem `derangeCount_rec`
- bounded labelled SET-star identity theorem `perm_eq_set_star_derange` for `n ≤ 8`, each case via `native_decide`

验证：
- `lake build AnalyticCombinatorics.PartA.Ch2.Derangements`
- 通过：`Build completed successfully`
