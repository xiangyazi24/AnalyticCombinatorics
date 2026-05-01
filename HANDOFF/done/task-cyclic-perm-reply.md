Done.

- Added `AnalyticCombinatorics/Examples/CyclicPermutations.lean`.
- Defined `IsCyclicPermutation` as the single-orbit predicate on `Equiv.Perm (Fin n)`, with `CyclicPermutation n` as the subtype.
- Added `cyclicPermutationCount`, the positive-size bridge to `labelCycCount Atom`, and sanity examples for sizes 1 through 5.
- Added the new example file to the root `AnalyticCombinatorics.lean` imports.

Verification:

- `lake env lean AnalyticCombinatorics/Examples/CyclicPermutations.lean`
- `lake build`

Both passed. No new `sorry`/`admit`/`axiom` in the new file.
