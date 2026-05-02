# Task — Tetranacci count sanity beyond n=22

**File:** `AnalyticCombinatorics/Examples/Tetranacci.lean` (append)

The file currently has `tetraClass.count n` sanity through `n = 22`. Extend through `n = 25`.

The Tetranacci recurrence is `T(n) = T(n-1)+T(n-2)+T(n-3)+T(n-4)`, with the existing helper lemmas `tetraClass_count_*` and the `tetraClass_count_eq_tetra` (or equivalent) bridge. Compute the next values (T_23, T_24, T_25) yourself from the recurrence; T_22 = 1055026 is the current top.

Use the same proof shape as the existing entries (`rw [...]; decide` or `native_decide`).

If `decide` / `native_decide` blows up at some n=k, document the threshold and stop there with a comment.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-tetra-extras5-reply.md.
- **ONLY modify `AnalyticCombinatorics/Examples/Tetranacci.lean`.** Local instances if needed.
