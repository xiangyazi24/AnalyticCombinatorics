# Task — Padovan compositions example

**File:** `AnalyticCombinatorics/Examples/Padovan.lean` (NEW)

Compositions of `n` into parts in `{2, 3}` are counted by `P_n` with `P_0 = 1, P_1 = 0, P_2 = 1, P_3 = 1, P_4 = 1, P_5 = 2, P_6 = 2, P_7 = 3, P_8 = 4, P_9 = 5, P_10 = 7`. (Padovan-like, OEIS A000931 shifted.)

## What to build

1. `step23Class : CombinatorialClass` defined as `atomOfSize 2 + atomOfSize 3` (use `disjSum` like `Examples/Tribonacci.lean` does for `step123Class`).
2. `padovanClass = seqClass step23Class h0` with `h0 : step23Class.count 0 = 0`.
3. Sanity examples for `padovanClass.count n` at `n = 0..10` matching `1, 0, 1, 1, 1, 2, 2, 3, 4, 5, 7`. Use `decide` / `native_decide`.
4. State the OGF identity `padovanClass.ogfZ * (1 - X^2 - X^3) = 1` — by analogy with `tribClass`'s OGF identity. Only attempt if the parallel proof goes through cleanly.
5. Add the new example file to `AnalyticCombinatorics.lean` import list.

## Hard constraints

- Build green.
- No new sorrys.
- Read `Examples/Tribonacci.lean` first to copy its disj-sum + sequence pattern.
- Reply at HANDOFF/outbox/task-padovan-reply.md.
- If step 4 doesn't go through quickly, skip and ship 1–3 + a TODO comment.
