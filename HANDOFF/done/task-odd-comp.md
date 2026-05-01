# Task — Compositions into odd parts → Fibonacci

**File:** `AnalyticCombinatorics/Examples/CompositionsOdd.lean` (NEW)

A composition of `n` whose parts are all **odd** is counted by `F_n` (Fibonacci with `F_0 = 0, F_1 = 1, F_2 = 1, F_3 = 2, F_4 = 3, F_5 = 5, F_6 = 8, F_7 = 13, F_8 = 21, F_9 = 34, F_10 = 55`). Convention: the empty composition counts the case `n = 0` with one element.

So `count 0 = 1`, `count 1 = 1`, `count 2 = 1`, `count 3 = 2`, `count 4 = 3`, etc. — same as Fibonacci `F_{n+1}` with appropriate convention.

(Verify the exact shift by reading F&S or computing small cases. The standard result: number of compositions of `n` into odd parts = `F_n` for `n ≥ 1`, with `count 0 = 1`. So values `1, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, ...` for `n = 0, 1, 2, ...` — that is `F_{n}` shifted such that index 0 is `1`.)

## What to build

1. `oddPartClass : CombinatorialClass` defined as `disjSum`-fold over `atomOfSize 1`, `atomOfSize 3`, `atomOfSize 5`, ... — but since we can't have an infinite disjoint sum easily, instead define directly:

   `oddPartClass : CombinatorialClass` with `Obj := { n : ℕ // n.Odd ∧ 0 < n }`, `size := Subtype.val`. (Or: `{ n : ℕ // n % 2 = 1 }`.)

2. `oddCompClass = seqClass oddPartClass h0` with `h0 : oddPartClass.count 0 = 0`.

3. Sanity examples for `oddCompClass.count n` at `n = 0..6` matching the Fibonacci values (compute small cases: `n=0 → 1` (empty), `n=1 → 1` (`[1]`), `n=2 → 1` (`[1,1]`), `n=3 → 2` (`[3]`, `[1,1,1]`), `n=4 → 3` (`[3,1]`, `[1,3]`, `[1,1,1,1]`), `n=5 → 5`, `n=6 → 8`).

4. (TODO comment) note the `count n = Nat.fib (n+1)` connection — don't prove unless quick.

5. Add to `AnalyticCombinatorics.lean` import list.

## Hard constraints

- Build green.
- No new sorrys (TODOs as comments are fine).
- Read `Examples/Compositions.lean` for `posIntClass` / `compositionClass` patterns. The "subtype with a predicate" pattern may need a Fintype instance — check `Examples/Compositions.lean`'s `posIntGe2Class` for how it handles that.
- Reply at HANDOFF/outbox/task-odd-comp-reply.md.
- If the Subtype + Fintype dance is awkward, document the impedance and ship just sanity through `n = 4` or so.
