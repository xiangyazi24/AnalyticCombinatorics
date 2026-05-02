# Task — Dyck path count sanity beyond n=18

**File:** `AnalyticCombinatorics/Examples/DyckPaths.lean` (append)

The file has `dyckPathClass.count n` sanity through `n = 18` (matching Catalan numbers C_n). Extend through `n = 21`.

Catalan: C_19 = 1767263190, C_20 = 6564120420, C_21 = 24466267020.

Use the existing helper lemma bridging dyckPath count to Catalan (look at the n=18 entry for the exact tactic) followed by `decide` / `native_decide`.

If elaboration blows up at some n=k, document the threshold and stop there.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-dyck-extras1-reply.md.
- **ONLY modify `AnalyticCombinatorics/Examples/DyckPaths.lean`.** Local instances if needed.
