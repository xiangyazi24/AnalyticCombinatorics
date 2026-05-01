# Task — Fibonacci compositions bivariate by number of parts

**File:** `AnalyticCombinatorics/Examples/Fibonacci.lean` (append)

`fibClass` is compositions of `n` into parts in `{1, 2}`. By analogy with `tribNumParts` / `tetraNumParts` / `padovanNumParts`, add:

1. `fibNumParts : Parameter fibClass`. (Note: the file already has `fibNumParts` per memory — read first to confirm; if it's already there, skip step 1.)

2. Sanity examples for `fibClass.jointCount fibNumParts n k` at small `(n, k)`:

   - `(0, 0) = 1`
   - `(1, 1) = 1`
   - `(2, 1) = 1`  (`[2]`)
   - `(2, 2) = 1`  (`[1,1]`)
   - `(3, 2) = 2`  (`[1,2]`, `[2,1]`)
   - `(3, 3) = 1`  (`[1,1,1]`)
   - `(4, 2) = 1`  (`[2,2]`)
   - `(4, 3) = 3`  (`[1,1,2]`, `[1,2,1]`, `[2,1,1]`)
   - `(4, 4) = 1`  (`[1,1,1,1]`)
   - `(5, 3) = 3`  (`[1,2,2]`, `[2,1,2]`, `[2,2,1]`)
   - `(5, 4) = 4`  (`[1,1,1,2]` and permutations)
   - `(5, 5) = 1`

   Use `decide`/`native_decide`.

3. (Optional) Sum identity: `∑_k jointCount n k = fib(n+1)` for some `n` like `n = 5` (sum should be `8`).

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-fib-numparts-reply.md.
- If `fibNumParts` already exists, just add the sanity examples.
