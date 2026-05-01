# Task — closed form for stringClass cartProd

**File:** `AnalyticCombinatorics/Examples/Strings.lean` (append)

We just added sanity for `(stringClass.cartProd stringClass).count n = (n+1) * 2^n` at small `n`. Try the **closed form** as a real theorem:

```lean
theorem stringClass_cartProd_stringClass_count
    (n : ℕ) :
    (stringClass.cartProd stringClass).count n = (n + 1) * 2 ^ n := by
  sorry
```

(Adjust the name to match the file's convention.)

## Suggested approach

`cartProd_count` gives `∑_{(i,j) ∈ antidiagonal n} 2^i * 2^j = ∑ 2^n` over `(n+1)` summands = `(n+1) * 2^n`.

Use:
- `cartProd_count` to expand
- `stringClass_count_eq_pow` to rewrite each summand to `2^i * 2^(n-i)`
- `pow_add` (i.e. `2^i * 2^(n-i) = 2^n`) — hold `i+j=n` from antidiagonal membership
- `Finset.sum_const`, `Finset.card_antidiagonal n = n+1`

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-string-conv-reply.md.
- Don't introduce axioms. If the proof gets stubborn at one step, document the blocker.
