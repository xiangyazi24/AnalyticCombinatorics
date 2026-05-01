# Task — Tribonacci numParts bivariate sanity at n=5

**File:** `AnalyticCombinatorics/Examples/Tribonacci.lean` (append)

The file has `tribNumParts` bivariate sanity through `n = 4`. Extend with `n = 5`:

Compositions of 5 into parts in `{1,2,3}`:
- `(5, 2) = ?` — pairs `(2,3),(3,2),(1,4)`-no 4 disallowed,(2,3),(3,2). So just `[2,3]` and `[3,2]`. = 2
- `(5, 3) = ?` — triples summing to 5: `[1,1,3], [1,3,1], [3,1,1], [1,2,2], [2,1,2], [2,2,1]` = 6
- `(5, 4) = ?` — quadruples summing to 5 with parts ≤ 3: `[1,1,1,2], [1,1,2,1], [1,2,1,1], [2,1,1,1]` = 4
- `(5, 5) = ?` — `[1,1,1,1,1]` = 1

Total: `2 + 6 + 4 + 1 = 13 = T_5`. ✓

Add 4 sanity examples for `(5, k)` with k = 2, 3, 4, 5.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-trib-numparts-extras-reply.md.
