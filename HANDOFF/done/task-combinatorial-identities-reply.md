Done.

Created `AnalyticCombinatorics/PartA/Ch1/CombinatorialIdentities.lean` with finite `native_decide` checks for:

- Vandermonde at `(5,3,4)`, including the expanded arithmetic check.
- Hockey-stick at `(n,r) = (5,2)`.
- Pascal's rule for `1 <= k <= n <= 8`.
- Binomial sum, alternating sum over `Int`, square-sum, and weighted-sum identities over the requested ranges.
- Double-counting identities over the requested ranges.
- A local recursive Catalan sequence, checked against the central-binomial formula for `n = 0..10` and convolution for `n = 0..8`.

Also added the new module to `AnalyticCombinatorics.lean`.

Verification:

- `lake build AnalyticCombinatorics.PartA.Ch1.CombinatorialIdentities`
- `lake build AnalyticCombinatorics`

Both completed successfully.
