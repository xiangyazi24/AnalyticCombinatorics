# Task — large Schröder number sanity beyond n=15

**File:** `AnalyticCombinatorics/Examples/SchroderTrees.lean` (append)

The file has `largeSchroderNumber` sanity rows (`example : largeSchroderNumber k = ... := by decide`) through `k = 15`. Extend through `k = 18`.

Compute the next values yourself from the existing definition (or the recurrence S(n) = ((6n-3)·S(n-1) − (n-2)·S(n-2)) / (n+1) for large Schröder numbers, OEIS A006318 starting 1,2,6,22,90,394,...).

Use `decide` (matching existing style); if it blows up at some k, switch to `native_decide` and/or document a threshold.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-schr-extras5-reply.md.
- **ONLY modify `AnalyticCombinatorics/Examples/SchroderTrees.lean`.** Local instances if needed.
