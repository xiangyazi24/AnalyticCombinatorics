# Task — cyclic permutation count sanity beyond n=20

**File:** `AnalyticCombinatorics/Examples/CyclicPermutations.lean` (append)

The file has `labelCycCount Atom n = (n-1)!` sanity through `n = 20`. Extend through `n = 23`:
- `labelCycCount Atom 21 = 2432902008176640000` (= 20!)
- `labelCycCount Atom 22 = 51090942171709440000` (= 21!)
- `labelCycCount Atom 23 = 1124000727777607680000` (= 22!)

Use the existing pattern. Use `native_decide` if `decide` slows.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-cyc-extras5-reply.md.
- **ONLY modify `AnalyticCombinatorics/Examples/CyclicPermutations.lean`.** Local instances if needed.
