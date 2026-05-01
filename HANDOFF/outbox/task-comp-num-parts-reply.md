Done.

- Added `numParts : Parameter compositionClass := List.length`.
- Added four completed sanity examples for `(n,k) = (0,0), (1,1), (2,1), (2,2)`.
- Proofs use direct uniqueness of the filtered level Finsets.

Verification:

- `lake env lean AnalyticCombinatorics/Examples/Compositions.lean`
- `lake build`
