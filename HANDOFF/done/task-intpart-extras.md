# Task — IntegerPartitions count sanity beyond p_6

**File:** `AnalyticCombinatorics/Examples/IntegerPartitions.lean` (append)

The file already verifies `p_0..p_6 = 1, 1, 2, 3, 5, 7, 11`. Push further: add explicit sanity examples for `p_7 = 15, p_8 = 22, p_9 = 30, p_10 = 42`.

Use the same tactic the existing examples use (probably `decide` or `native_decide` after the `count = Fintype.card (Nat.Partition n)` bridge). If `decide` blows up at `p_8` or beyond, switch to `native_decide`. If `native_decide` also blows up, **document the threshold** — partition counting via `Fintype.card` may not be Mathlib's most efficient route.

If neither tactic works at `n = 7` already, document that as a blocker and stop (don't fall back to manual constructions).

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-intpart-extras-reply.md.
