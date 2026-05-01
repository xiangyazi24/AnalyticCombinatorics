# Task — Tribonacci compositions example

**File:** `AnalyticCombinatorics/Examples/Tribonacci.lean` (NEW)

Compositions of `n` into parts in `{1, 2, 3}` are counted by the tribonacci-like sequence `T_n` with `T_0 = 1, T_1 = 1, T_2 = 2, T_3 = 4, T_4 = 7, T_5 = 13, T_6 = 24, T_7 = 44`.

Note: this is OEIS A000073 shifted; the standard tribonacci recurrence here is `T_n = T_{n-1} + T_{n-2} + T_{n-3}` with the seed `T_0=1, T_1=1, T_2=2`.

## What to build

1. `step123Class : CombinatorialClass` defined as `atomOfSize 1 + atomOfSize 2 + atomOfSize 3` (use `disjSum` like `Examples/Fibonacci.lean` does for `stepClass = atomOfSize 1 + atomOfSize 2`).
2. `tribClass = seqClass step123Class h0` where `h0 : step123Class.count 0 = 0`.
3. Sanity examples for `tribClass.count n` at `n = 0..7` matching `1, 1, 2, 4, 7, 13, 24, 44`. Use `decide` / `native_decide`.
4. (Optional, only if quick) state the OGF identity `tribClass.ogfZ * (1 - X - X^2 - X^3) = 1` style result, by analogy with `fibClass_ogfZ_mul_one_sub_X_sub_X_sq` — only attempt if the parallel proof goes through cleanly. Otherwise skip.
5. Add to `AnalyticCombinatorics.lean` imports if such an aggregate exists.

## Hard constraints

- Build green.
- No new sorrys (TODOs as comments are fine).
- Read `Examples/Fibonacci.lean` first to copy the binary-step pattern correctly.
- Reply at HANDOFF/outbox/task-tribonacci-reply.md.
- If step 4 doesn't go through in one shot, skip it and ship steps 1–3.
