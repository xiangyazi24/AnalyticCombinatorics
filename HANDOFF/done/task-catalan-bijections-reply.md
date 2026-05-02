Done.

Created:
- `AnalyticCombinatorics/PartA/Ch1/CatalanBijections.lean`

Verified:
- `lake build AnalyticCombinatorics.PartA.Ch1.CatalanBijections`

Note:
- `dyckCount` is recorded as the Catalan semilength counting sequence
  `Nat.centralBinom n / (n + 1)`. Re-enumerating `dyckPathClass` through
  `n = 8` in this new file was too slow; `LatticePaths.lean` already contains
  the explicit Dyck-path finite-class checks for the initial values.
