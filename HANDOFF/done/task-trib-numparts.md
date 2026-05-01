# Task — Tribonacci bivariate by number of parts

**File:** `AnalyticCombinatorics/Examples/Tribonacci.lean` (append)

`tribClass` is compositions of `n` into parts in `{1, 2, 3}`. Add a Parameter recording the number of parts, plus small bivariate sanity. Mirrors `padovanNumParts` already in `Examples/Padovan.lean`.

## What to add

1. `tribNumParts : Parameter tribClass` returning the length of the underlying composition list.

2. Sanity examples for `tribClass.jointCount tribNumParts n k` at small `(n, k)`:

   - `(0, 0) = 1`
   - `(1, 1) = 1`  (`[1]`)
   - `(2, 1) = 1`  (`[2]`)
   - `(2, 2) = 1`  (`[1,1]`)
   - `(3, 1) = 1`  (`[3]`)
   - `(3, 2) = 2`  (`[1,2]`, `[2,1]`)
   - `(3, 3) = 1`  (`[1,1,1]`)
   - `(4, 2) = 3`  (`[1,3]`, `[3,1]`, `[2,2]`)
   - `(4, 3) = 3`  (`[1,1,2]`, `[1,2,1]`, `[2,1,1]`)
   - `(4, 4) = 1`  (`[1,1,1,1]`)

   Use `decide`/`native_decide`. (Total at n=4: `1 + 3 + 3 + 1 = 7 = T_4`. ✓)

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-trib-numparts-reply.md.
- Read `Examples/Padovan.lean` for the pattern.
