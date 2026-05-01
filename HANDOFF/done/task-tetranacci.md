# Task — Tetranacci compositions example

**File:** `AnalyticCombinatorics/Examples/Tetranacci.lean` (NEW)

Compositions of `n` into parts in `{1, 2, 3, 4}` are counted by `Q_n` with seed `1, 1, 2, 4, 8, 15, 29, 56, 108`. (Tetranacci-style: `Q_n = Q_{n-1} + Q_{n-2} + Q_{n-3} + Q_{n-4}` with `Q_0 = 1, Q_1 = 1, Q_2 = 2, Q_3 = 4`.)

## What to build

1. `step1234Class : CombinatorialClass` defined as `atomOfSize 1 + atomOfSize 2 + atomOfSize 3 + atomOfSize 4` (use `disjSum`, by analogy with `Examples/Tribonacci.lean`'s `step123Class`).
2. `tetraClass = seqClass step1234Class h0` with `h0 : step1234Class.count 0 = 0`.
3. Sanity examples for `tetraClass.count n` at `n = 0..8` matching `1, 1, 2, 4, 8, 15, 29, 56, 108`. Use `decide` / `native_decide`.
4. State the OGF identity `tetraClass.ogfZ * (1 - X - X^2 - X^3 - X^4) = 1` — by direct analogy with `tribClass`'s OGF identity. Only attempt if the parallel proof goes through cleanly.
5. Add to `AnalyticCombinatorics.lean` import list.

## Hard constraints

- Build green.
- No new sorrys (TODOs as comments are fine).
- Read `Examples/Tribonacci.lean` first to copy the pattern.
- Reply at HANDOFF/outbox/task-tetranacci-reply.md.
- If step 4 doesn't go through quickly, skip it and ship 1–3 + a TODO comment.
