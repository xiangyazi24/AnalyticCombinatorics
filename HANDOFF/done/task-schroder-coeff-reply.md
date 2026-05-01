Done.

- Added the OGF coefficient identity in `AnalyticCombinatorics/Examples/SchroderTrees.lean`:
  `SchroderTree.asClass.ogf.coeff n = SchroderTree.asClass.count n`.
- Did not add the requested `SchroderTree.asClass.count 1 = 2`, `2 = 6`, `3 = 22` examples: those values are already present for `largeSchroderNumber`, while `asClass` is documented in this file as the uncolored class whose positive coefficients are little Schroder numbers.
- No new `sorry`s.
- Verified with:
  - `lake env lean AnalyticCombinatorics/Examples/SchroderTrees.lean`
  - `lake build`
