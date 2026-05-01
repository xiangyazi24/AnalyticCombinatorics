# Task — Pairs of binary strings cartProd sanity

**File:** `AnalyticCombinatorics/Examples/Strings.lean` (append)

The class `stringClass.cartProd stringClass` should have count `4^n` (since each summand-pair `(i, n-i)` contributes `2^i · 2^(n-i) = 2^n` and there are `n+1` such splits, total `(n+1) · 2^n`...).

Wait — `cartProd_count n = ∑_{i ≤ n} A.count i * B.count (n-i)`. For `A = B = stringClass`:

`(stringClass.cartProd stringClass).count n = ∑_{i=0}^n 2^i · 2^(n-i) = (n+1) · 2^n`.

That's the convolution.

## What to add

Sanity examples for `(stringClass.cartProd stringClass).count n` at `n = 0..5`:

- `n = 0`: `1 · 2^0 = 1`
- `n = 1`: `2 · 2^1 = 4`
- `n = 2`: `3 · 2^2 = 12`
- `n = 3`: `4 · 2^3 = 32`
- `n = 4`: `5 · 2^4 = 80`
- `n = 5`: `6 · 2^5 = 192`

Use `cartProd_count` (already in `Ch1/CombinatorialClass.lean`) + the existing `stringClass_count_eq_pow` to discharge.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-string-cartprod-reply.md.
- If the convolution sum is awkward to evaluate symbolically, fall back to `decide`/`native_decide` after rewriting via `cartProd_count`.
