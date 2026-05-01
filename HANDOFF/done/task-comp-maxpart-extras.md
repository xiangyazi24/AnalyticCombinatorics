# Task — compMaxPart bivariate sanity beyond n=4

**File:** `AnalyticCombinatorics/Examples/Compositions.lean` (append)

The file has `compositionClass.jointCount compMaxPart n k` sanity through `n = 4`. Extend to `n = 5, 6`:

For `n = 5`:
- `(5, 1) = 1` (`[1,1,1,1,1]`)
- `(5, 2) = ?` — need to count compositions of 5 with max part 2: `[2,2,1], [2,1,2], [1,2,2], [2,1,1,1], [1,2,1,1], [1,1,2,1], [1,1,1,2]` = 7
- `(5, 3) = ?` — max part 3: `[3,2], [2,3], [3,1,1], [1,3,1], [1,1,3]` = 5
- `(5, 4) = 2` — max part 4: `[4,1], [1,4]` = 2
- `(5, 5) = 1` — `[5]`

Total: `1 + 7 + 5 + 2 + 1 = 16 = 2^4 = compositionClass.count 5`. ✓

For `n = 6`:
- `(6, 1) = 1`
- `(6, 2) = ?` — count via decide
- `(6, 3) = ?`
- `(6, 4) = ?`
- `(6, 5) = 2`  (`[5,1], [1,5]`)
- `(6, 6) = 1`  (`[6]`)

Use `decide` / `native_decide`. Verify the sum equals `2^5 = 32`.

If decoder is heavy at n=6, ship just n=5 plus `(6, 5) = 2, (6, 6) = 1`. Document the threshold.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-comp-maxpart-extras-reply.md.
