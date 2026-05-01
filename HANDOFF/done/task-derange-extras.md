# Task — derangement small-value sanity

**File:** `AnalyticCombinatorics/Examples/Derangements.lean` (append)

Add explicit `decide`/`native_decide` sanity for derangement counts at small `n`. The classical sequence is `D_0 = 1, D_1 = 0, D_2 = 1, D_3 = 2, D_4 = 9, D_5 = 44, D_6 = 265, D_7 = 1854, D_8 = 14833, D_9 = 133496`.

Read the file first and confirm whether `derangementClass.count n = Nat.numDerangements n` is already established. If yes, add **at least four** new explicit `decide` lemmas at values not already covered (look at existing `example` and `lemma` lines), preferably at the larger end (D_9, D_10, etc.) where compute is heavier — switch to `native_decide` if `decide` is slow.

If `Nat.numDerangements` evaluation is the bottleneck, the existing `derangementClass_count_eq_numDerangements` gives a route: `(derangementClass.count n) = Nat.numDerangements n` rewritten then `decide`/`native_decide` on the RHS.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-derange-extras-reply.md.
- Document any blocker (esp. compute timeout) — don't paper over.
