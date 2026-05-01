已完成。

改动：
- 在 `AnalyticCombinatorics/Examples/Derangements.lean` 追加了 `D(X) * exp(X) = permClass.egf`：
  `derangementClass_egf_mul_exp_eq_permClass_egf`
- 追加了用户指定的系数卷积例子，无占位证明。
- 证明路线是先由 `numDerangements_succ` 得到 `(1 - X) * derangementClass.egf = exp(-X)`，再用 `exp(X) * exp(-X) = 1` 和 `permClass.egf = 1/(1-X)`。

验证：
- `lake env lean AnalyticCombinatorics/Examples/Derangements.lean`
- `lake build`

结果：build green。
