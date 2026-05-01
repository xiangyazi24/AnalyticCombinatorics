Option taken: B.

Implemented `MotzTree.motzClass_count_recurrence` in
`AnalyticCombinatorics/Examples/MotzkinTrees.lean`, with
`MotzTree.motzClass` as an alias for the existing `asClass`. The theorem
derives the range-indexed Motzkin recurrence from the existing
`count_succ_succ` antidiagonal recurrence via
`Finset.Nat.sum_antidiagonal_eq_sum_range_succ`.

Also added a numerical recurrence check at `n = 3`:
`count 5 = count 4 + sum_{k=0}^3 count k * count (3-k)`.

Verification:
- `lake env lean AnalyticCombinatorics/Examples/MotzkinTrees.lean`
- `lake build`
- `rg -n "sorry|axiom" AnalyticCombinatorics/Examples/MotzkinTrees.lean`

No new sorrys or axioms.
