# Task — quatStringClass cartProd closed form

**File:** `AnalyticCombinatorics/Examples/Strings.lean` (append)

By analogy with `stringClass_cartProd_count` (= `(n+1) * 2^n`), prove:

```lean
theorem quatStringClass_cartProd_count (n : ℕ) :
    (quatStringClass.cartProd quatStringClass).count n = (n + 1) * 4 ^ n := by
  sorry
```

Mirror the proof pattern of `stringClass_cartProd_count`:
- `cartProd_count` to expand
- `quatStringClass_count_eq_pow` to rewrite each summand to `4^i * 4^(n-i)`
- `pow_add` to collapse to `4^n` per summand
- `Finset.sum_const` + `Finset.Nat.card_antidiagonal n = n+1`

Add 3 sanity examples at `n = 0, 2, 5` (values `1, 48, 7680`).

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-quat-cartprod-reply.md.
- **ONLY modify `AnalyticCombinatorics/Examples/Strings.lean`.** Local instances if needed.
