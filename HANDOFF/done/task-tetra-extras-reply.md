Done.

Changed:
- Added `tetraClass.count` sanity lemmas and examples for `n = 9..14`:
  `208, 401, 773, 1490, 2872, 5536`.
- Kept the existing proof style: recurrence lemma + `rw` + `decide`.
- No new `sorry`s.

Verified:
- `lake env lean AnalyticCombinatorics/Examples/Tetranacci.lean`
- `lake build`
