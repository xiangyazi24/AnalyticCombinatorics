# Task — Padovan numParts bivariate sanity at n=7,8

**File:** `AnalyticCombinatorics/Examples/Padovan.lean` (append)

The file has `padovanNumParts` bivariate sanity at small `(n, k)`. Extend with:

For `n = 7` (parts in `{2, 3}`, sum to 7):
- `(7, 3) = 3`  (`[2,2,3]`, `[2,3,2]`, `[3,2,2]`)
- (other `(7, k)` are 0 since min part 2 means k ≤ 3 for n=7)

For `n = 8`:
- `(8, 3) = 3`  (`[2,3,3]`, `[3,2,3]`, `[3,3,2]`)
- `(8, 4) = 1`  (`[2,2,2,2]`)

Add 3 sanity examples (or any subset that lands cleanly).

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-padovan-numparts-extras-reply.md.
- **ONLY modify `AnalyticCombinatorics/Examples/Padovan.lean`.** Do not touch other files. If the build needs an instance, add it locally to the same file.
