# Task — Padovan bivariate by number of parts

**File:** `AnalyticCombinatorics/Examples/Padovan.lean` (append)

`padovanClass` (already in the file) is compositions of `n` into parts in `{2, 3}`. Add a Parameter recording the number of parts and small bivariate sanity.

## What to add

1. `padovanNumParts : Parameter padovanClass` returning the length of the underlying composition list. (Use whatever pattern `Examples/Compositions.lean`'s `numParts` uses.)

2. Sanity examples for `padovanClass.jointCount padovanNumParts n k` at small `(n, k)`:

   - `(2, 1) = 1`  (`[2]`)
   - `(3, 1) = 1`  (`[3]`)
   - `(4, 2) = 1`  (`[2,2]`)
   - `(5, 2) = 2`  (`[2,3]`, `[3,2]`)
   - `(6, 2) = 1`  (`[3,3]`)
   - `(6, 3) = 1`  (`[2,2,2]`)
   - `(7, 3) = 3`  (`[2,2,3]`, `[2,3,2]`, `[3,2,2]`)

   Use `decide`/`native_decide`.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-padovan-numparts-reply.md.
