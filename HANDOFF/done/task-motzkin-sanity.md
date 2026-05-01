# Task — MotzkinTrees small count sanity

**File:** `AnalyticCombinatorics/Examples/MotzkinTrees.lean` (append)

Add explicit `decide` / `native_decide` sanity values for Motzkin counts at small n. The Motzkin numbers are 1, 1, 2, 4, 9, 21, 51, 132 (at n = 0..7 if we count the leaf as size 1, so the values land at sizes 1, 2, 3, ...). Match the convention already used in the file — read the existing `motzkin_size_*` example or count helper first.

Add at least four sanity examples covering the next two values past whatever's already there, plus one or two restated identities (e.g. `motzClass.count 1 + 1 = motzClass.count 1 + 1` style is fine if compute is heavy — pick whatever decides cleanly).

If `decide` times out, fall back to `native_decide`.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-motzkin-sanity-reply.md.
- If the convention forces values you can't recompute, **document a blocker** in the reply rather than guessing.
