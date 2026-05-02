# Task — Motzkin count sanity beyond n=21

**File:** `AnalyticCombinatorics/Examples/MotzkinTrees.lean` (append)

The file currently has `motzClass.count n` sanity through `n = 21`. Extend through `n = 24`.

Use the existing helper lemma (`motzClass_count_eq_motzkinNumber` or analogous) followed by `decide` / `native_decide` matching the existing pattern. Compute the target values yourself from the helper or the Motzkin recurrence `M(n+2) = M(n+1) + Σ_{k=0}^{n} M(k) M(n-k)`.

If the elaboration blows up at some n=k, document the threshold and stop there.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-motz-extras5-reply.md.
- **ONLY modify `AnalyticCombinatorics/Examples/MotzkinTrees.lean`.** Local instances if needed.
