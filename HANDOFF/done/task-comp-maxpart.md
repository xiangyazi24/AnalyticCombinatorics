# Task — Compositions bivariate by max part

**File:** `AnalyticCombinatorics/Examples/Compositions.lean` (append)

`compositionClass` (already in the file) is compositions of `n` into positive integer parts. Add a `Parameter` recording the maximum part of the composition (with the convention that the empty composition has max-part `0`, so `n = 0` only meets `k = 0`). Then add small bivariate sanity examples.

## What to add

1. `compMaxPart : Parameter compositionClass` returning the max part. For the empty composition, return `0`.

2. Sanity examples for `compositionClass.jointCount compMaxPart n k` at small `n`:

   - `(0, 0) = 1`
   - `(1, 1) = 1`
   - `(2, 1) = 1`  (only `[1,1]`)
   - `(2, 2) = 1`  (only `[2]`)
   - `(3, 1) = 1`  (`[1,1,1]`)
   - `(3, 2) = 2`  (`[1,2]`, `[2,1]`)
   - `(3, 3) = 1`  (`[3]`)
   - `(4, 1) = 1`
   - `(4, 2) = 4`  (`[2,2]`, `[1,1,2]`, `[1,2,1]`, `[2,1,1]`)
   - `(4, 3) = 2`  (`[1,3]`, `[3,1]`)
   - `(4, 4) = 1`  (`[4]`)

   Use `decide`/`native_decide`.

## Hard constraints

- Build green.
- No new sorrys.
- Read `Examples/Compositions.lean` first to see the existing `numParts` Parameter pattern; copy that pattern.
- Reply at HANDOFF/outbox/task-comp-maxpart-reply.md.
- If extracting "max part of the underlying List ℕ" is awkward (e.g. `List.maximum` returns `Option` or `WithBot`), pick a sensible default for empty (0) and document the convention.
