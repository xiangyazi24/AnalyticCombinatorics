# Task — Composition first-part Parameter + sanity

**File:** `AnalyticCombinatorics/Examples/Compositions.lean` (append)

`compositionClass` has compositions of `n` into positive parts. Add a `Parameter` recording the first part (0 if empty composition), plus small bivariate sanity.

## What to add

1. `compFirstPart : Parameter compositionClass` returning the first part (0 if empty).

2. Sanity examples for `compositionClass.jointCount compFirstPart n k` at small `(n, k)`. Closed form: for `1 ≤ k ≤ n-1`, # compositions of `n` with first part = `k` equals # compositions of `n-k` = `2^(n-k-1)`. For `k = n`, it's 1 (the composition `[n]`). For `k = 0` and `n ≠ 0`, it's 0.

   Examples:
   - `(0, 0) = 1`  (empty)
   - `(1, 1) = 1`  (`[1]`)
   - `(2, 1) = 1`  (`[1,1]`)
   - `(2, 2) = 1`  (`[2]`)
   - `(3, 1) = 2`  (`[1,1,1]`, `[1,2]`)
   - `(3, 2) = 1`  (`[2,1]`)
   - `(3, 3) = 1`  (`[3]`)
   - `(4, 1) = 4`  (compositions of 3 prefixed with 1 → 4 of them)
   - `(4, 2) = 2`  (compositions of 2 prefixed with 2)
   - `(4, 3) = 1`
   - `(4, 4) = 1`

   Use `decide`/`native_decide`.

3. (Optional) Sum identity: `∑ k ∈ image compFirstPart (level n), jointCount n k = compositionClass.count n` — should follow from the existing `jointCount_sum_eq_count` infrastructure.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-comp-firstpart-reply.md.
- Read existing `numParts`/`compMaxPart` Parameters for the pattern. Pick "0 if empty" convention for the first-part-of-empty case.
