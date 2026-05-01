# Task — ternaryStringClass bivariate parameter (count of zeros)

**File:** `AnalyticCombinatorics/Examples/Strings.lean` (append)

`ternaryStringClass` (already in the file) is sequences over `Fin 3` of length n. Add a `Parameter` recording the number of `0`-letters (i.e. occurrences of `(0 : Fin 3)`) and small bivariate sanity.

## What to add

1. `ternaryNumZero : Parameter ternaryStringClass` returning the number of `0`-letters in the underlying sequence. Pattern follows `stringNumTrue` already in the file.

2. Sanity examples for `ternaryStringClass.jointCount ternaryNumZero n k` at small `(n, k)`:

   - `(0, 0) = 1`
   - `(1, 0) = 2`  (just `[1]` or `[2]`)
   - `(1, 1) = 1`  (`[0]`)
   - `(2, 0) = 4`  (length-2 strings without any 0: `2 · 2 = 4`)
   - `(2, 1) = 4`  (one 0, one non-zero: 2 positions × 2 choices)
   - `(2, 2) = 1`  (`[0, 0]`)
   - `(3, 1) = 12`  (3 positions for 0, 4 ways for the rest = `3 · 4`)
   - `(3, 2) = 6`  (3 positions for non-zero, 2 choices each = `3 · 2`)

   Use `decide`/`native_decide`.

3. Sum identity (optional): `∑ k in (level n).image ternaryNumZero, jointCount n k = 3^n` for some small n (e.g. `n = 3`, sum should equal `27`).

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-ternary-bivariate-reply.md.
- Don't refactor existing string defs.
