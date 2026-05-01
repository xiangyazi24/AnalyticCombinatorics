# Task — Tetranacci numParts bivariate sanity at n=5

**File:** `AnalyticCombinatorics/Examples/Tetranacci.lean` (append)

The file has `tetraNumParts` bivariate sanity through n=4. Extend with `n = 5`:

Compositions of 5 into parts in `{1,2,3,4}`:
- `(5, 1) = 0`  (no part = 5 since max part is 4)
- `(5, 2) = 4`  (`[1,4],[4,1],[2,3],[3,2]`)
- `(5, 3) = 6`  (`[1,1,3],[1,3,1],[3,1,1],[1,2,2],[2,1,2],[2,2,1]`)
- `(5, 4) = 4`
- `(5, 5) = 1`

Total = 0+4+6+4+1 = 15 = T_5 ✓.

Add 4 sanity examples for k = 2..5.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-tetra-numparts-extras-reply.md.
- **ONLY modify `AnalyticCombinatorics/Examples/Tetranacci.lean`.** Do not touch other files. Local instances if needed.
