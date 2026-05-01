# Task — Tetranacci bivariate by number of parts

**File:** `AnalyticCombinatorics/Examples/Tetranacci.lean` (append)

`tetraClass` is compositions of `n` into parts in `{1, 2, 3, 4}`. By analogy with `tribNumParts` and `padovanNumParts`, add:

1. `tetraNumParts : Parameter tetraClass`.

2. Sanity examples for `tetraClass.jointCount tetraNumParts n k` at small `(n, k)`:

   - `(0, 0) = 1`
   - `(1, 1) = 1`
   - `(2, 1) = 1`  (`[2]`)
   - `(2, 2) = 1`  (`[1,1]`)
   - `(3, 1) = 1`  (`[3]`)
   - `(3, 2) = 2`  (`[1,2]`, `[2,1]`)
   - `(3, 3) = 1`  (`[1,1,1]`)
   - `(4, 1) = 1`  (`[4]`)
   - `(4, 2) = 3`  (`[1,3]`, `[3,1]`, `[2,2]`)
   - `(4, 3) = 3`
   - `(4, 4) = 1`

   Use `decide`/`native_decide`. Total at n=4 = 1+3+3+1 = 8 = T_4. ✓

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-tetra-numparts-reply.md.
- Read `Examples/Tribonacci.lean`'s `tribNumParts` for the pattern.
