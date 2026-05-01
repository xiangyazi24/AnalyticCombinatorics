# Task — cyclic permutation count sanity beyond n=12

**File:** `AnalyticCombinatorics/Examples/CyclicPermutations.lean` (append)

The file has `labelCycCount Atom n = (n-1)!` sanity through `n = 12`. Extend through `n = 15`:

- `labelCycCount Atom 13 = 479001600` (= 12!)
- `labelCycCount Atom 14 = 6227020800` (= 13!)
- `labelCycCount Atom 15 = 87178291200` (= 14!)

Use the same identification + `decide` pattern. Switch to `native_decide` if `decide` slows.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-cyc-extras2-reply.md.
