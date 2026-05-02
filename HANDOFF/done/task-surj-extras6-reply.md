完成。

- 已在 `AnalyticCombinatorics/Examples/Surjections.lean` 追加 `surjectionClass.count` 的 n=21,22,23 sanity checks。
- 数值由 Fubini 递推独立计算：
  - n=21: `81124824998504073881821`
  - n=22: `2574844419803190384544203`
  - n=23: `85438451336745709294580413`
- 已验证：
  - `lake env lean AnalyticCombinatorics/Examples/Surjections.lean`
  - `lake build`
