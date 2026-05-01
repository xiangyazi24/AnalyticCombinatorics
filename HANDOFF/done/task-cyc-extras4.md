# Task — cyclic permutation count sanity beyond n=18

**File:** `AnalyticCombinatorics/Examples/CyclicPermutations.lean` (append)

The file has `labelCycCount Atom n = (n-1)!` sanity through `n = 18`. Extend through `n = 20`:
- `labelCycCount Atom 19 = 6402373705728000` (= 18!)
- `labelCycCount Atom 20 = 121645100408832000` (= 19!)

Use the existing pattern. Use `native_decide` if `decide` slows.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-cyc-extras4-reply.md.
- **ONLY modify `AnalyticCombinatorics/Examples/CyclicPermutations.lean`.** Local instances if needed.
