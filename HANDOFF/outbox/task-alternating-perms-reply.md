Done.

Created `AnalyticCombinatorics/PartA/Ch2/AlternatingPerms.lean`.

Contents:
- `boustrophedon : ℕ → ℕ → ℕ`, using the Entringer/boustrophedon triangle with zero entries above the diagonal.
- `zigzagNumber : ℕ → ℕ`, with `zigzagNumber n = boustrophedon n n`.
- `tangentNumber : ℕ → ℕ` and `secantNumber : ℕ → ℕ`.
- `native_decide` checks for `E(0)..E(7)`, tangent values, secant values, diagonal values, and `secantNumber n = zigzagNumber (2 * n)` for `n ≤ 4`.

Also imported the new module from `AnalyticCombinatorics.lean`.

Verification:

```text
lake build AnalyticCombinatorics.PartA.Ch2.AlternatingPerms
```

passed.
