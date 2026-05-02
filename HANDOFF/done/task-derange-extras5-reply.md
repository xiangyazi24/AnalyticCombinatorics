Done.

- Extended `AnalyticCombinatorics/Examples/Derangements.lean` with sanity examples for `derangementClass.count 22`, `23`, and `24`.
- Values used:
  - `D22 = 413496759611120779881`
  - `D23 = 9510425471055777937262`
  - `D24 = 228250211305338670494289`
- Proof pattern matches the surrounding block: `rw [derangementClass_count_eq_numDerangements]` followed by `decide`.
- No elaboration threshold was hit through `n = 24`; no `native_decide` was needed.

Verification:

- `lake env lean AnalyticCombinatorics/Examples/Derangements.lean` passed.
- `lake build AnalyticCombinatorics.Examples.Derangements` passed.
- A full `lake build` reached and successfully built `AnalyticCombinatorics.Examples.Derangements`, then continued into unrelated later targets and did not return a final exit code in this run.
