Done.

- Extended `labelCycCount Atom n = (n-1)!` sanity checks through `n = 20`.
- Used the existing `rw [labelCycCount_Atom_succ]` + `decide` pattern.
- Verified:
  - `lake env lean AnalyticCombinatorics/Examples/CyclicPermutations.lean`
  - `lake build`
