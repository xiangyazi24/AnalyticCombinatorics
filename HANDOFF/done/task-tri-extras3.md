# Task — Triangulations sanity beyond n=18

**File:** `AnalyticCombinatorics/Examples/Triangulations.lean` (append)

The file currently has `triangulationClass.count n` sanity through `n = 18` (count 18 = 477638700). Extend through `n = 21`.

Triangulation counts are Catalan numbers: C(n) = (2n choose n) / (n+1).
C(19) = 1767263190, C(20) = 6564120420, C(21) = 24466267020.

Use the same proof shape as existing entries (likely `rw [...]; native_decide` or `decide`).

If `native_decide` times out at some n, document the threshold and stop there.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-tri-extras3-reply.md.
- **ONLY modify `AnalyticCombinatorics/Examples/Triangulations.lean`.** Local instances if needed.
