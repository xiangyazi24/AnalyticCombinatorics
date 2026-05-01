# Task — compFirstPart bivariate sanity beyond n=4

**File:** `AnalyticCombinatorics/Examples/Compositions.lean` (append)

The file has `compositionClass.jointCount compFirstPart n k` sanity through `n = 4`. Extend with `n = 5`:

For `n = 5`:
- `(5, 1) = 8`  (compositions of 4 prefixed with 1; #compositions of 4 = 2^3 = 8)
- `(5, 2) = 4`  (compositions of 3 prefixed with 2; #compositions of 3 = 2^2 = 4)
- `(5, 3) = 2`  (compositions of 2 prefixed with 3; #compositions of 2 = 2^1 = 2)
- `(5, 4) = 1`  (compositions of 1 prefixed with 4; just `[4,1]`)
- `(5, 5) = 1`  (`[5]`)

Total = 8+4+2+1+1 = 16 = 2^4 ✓

Add 5 sanity examples for `(5, k)` k=1..5.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-comp-firstpart-extras-reply.md.
- **ONLY modify `AnalyticCombinatorics/Examples/Compositions.lean`.** Local instances if needed.
