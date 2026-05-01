Done.

- Extended `tetraClass.count` sanity through `n = 22`:
  - `count 19 = 147312`
  - `count 20 = 283953`
  - `count 21 = 547337`
  - `count 22 = 1055026`
- Used the existing recurrence/count-lemma pattern with `decide`; `native_decide` was not needed.
- Verified:
  - `lake env lean AnalyticCombinatorics/Examples/Tetranacci.lean`
  - `lake build`

`lake build` completed successfully.
