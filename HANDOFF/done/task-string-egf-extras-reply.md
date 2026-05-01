Done.

- Appended the two requested zero-coefficient identities for `stringClass.egf` and `stringClass.ogf` to `AnalyticCombinatorics/Examples/Strings.lean`.
- Added `simp` to the OGF proof after `rw`, since Lean leaves `2 ^ 0 = 1`.
- Verification:
  - `lake env lean AnalyticCombinatorics/Examples/Strings.lean`
  - `lake build`
  - `rg "sorry" AnalyticCombinatorics/Examples/Strings.lean` found no matches.
