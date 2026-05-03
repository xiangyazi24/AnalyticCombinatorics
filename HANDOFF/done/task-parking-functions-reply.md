Done.

Created `AnalyticCombinatorics/PartA/Ch2/ParkingFunctions.lean`.

Included:
- `parkingFunctionCount (n : ℕ) : ℕ := (n + 1) ^ (n - 1)`, with `n = 0` check.
- Parking-function values for `n = 1..8` by `native_decide`.
- Cayley rooted-tree relation:
  `cayleyCount (n + 1) = (n + 1) * parkingFunctionCount n`.
- Equivalent quotient theorem:
  `parkingFunctionCount n = cayleyCount (n + 1) / (n + 1)`.
- Checked Cayley quotient agreement for `n = 1..8`.
- A small `ballotCount` formula with native sanity checks.

Verification:
- `lake build AnalyticCombinatorics.PartA.Ch2.ParkingFunctions`
- Result: success.
