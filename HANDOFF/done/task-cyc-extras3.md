# Task — cyclic permutation count sanity beyond n=15

**File:** `AnalyticCombinatorics/Examples/CyclicPermutations.lean` (append)

The file has `labelCycCount Atom n = (n-1)!` sanity through `n = 15`. Extend through `n = 18`:
- `labelCycCount Atom 16 = 1307674368000` (= 15!)
- `labelCycCount Atom 17 = 20922789888000` (= 16!)
- `labelCycCount Atom 18 = 355687428096000` (= 17!)

Use the existing identification + `decide`/`native_decide` pattern.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-cyc-extras3-reply.md.
- **ONLY modify `AnalyticCombinatorics/Examples/CyclicPermutations.lean`.** Local instances if needed.
