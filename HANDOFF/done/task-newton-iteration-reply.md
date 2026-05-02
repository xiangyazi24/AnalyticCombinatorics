Created `AnalyticCombinatorics/PartA/Ch1/Newton.lean`.

Proved:

- `trunc` and `agreeUpTo`, with coefficient/truncation agreement lemmas.
- A coefficient bootstrapping lemma for the Catalan equation:
  if `f` satisfies `f = 1 + X * f^2` up to order `N`, then it agrees with
  `binaryTreeClass.ogf` up to order `N`.
- The requested `catalan_bootstrap`.
- Explicit initial approximations:
  `catalanIter0`, `catalanIter1`, `catalanIter2`, with agreement through
  orders `1`, `2`, and `4`.
- `catalan_ogf_unique`: any `PowerSeries ℕ` root of
  `f = 1 + X * f ^ 2` is `binaryTreeClass.ogf`.

Verification:

- `lake build AnalyticCombinatorics.PartA.Ch1.Newton` passes.
