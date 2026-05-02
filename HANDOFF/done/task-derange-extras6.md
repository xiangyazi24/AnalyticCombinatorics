# Task — Derangements sanity beyond n=24

**File:** `AnalyticCombinatorics/Examples/Derangements.lean` (append)

The file has `derangementClass` sanity through n=24. Extend through n=27 (or as high as feasible).

Derangement counts D(n) = n! * sum_{k=0}^{n} (-1)^k/k!.
D(25)=9227046511766524160, D(26)=239902115640599345920, D(27)=6474957122295580339200.

Use the same proof patterns already in the file.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-derange-extras6-reply.md.
- **ONLY modify `AnalyticCombinatorics/Examples/Derangements.lean`.** Local instances if needed.
