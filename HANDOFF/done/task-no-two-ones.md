# Task — Binary strings without two consecutive 1s

**File:** `AnalyticCombinatorics/Examples/StringsNoConsecutiveOnes.lean` (NEW)

Binary strings of length `n` containing no two adjacent `true`s are counted by `F_{n+2}` (Fibonacci with `F_0=0, F_1=1, F_2=1, F_3=2, ...`). At `n = 0..6` the counts are `1, 2, 3, 5, 8, 13, 21`. F&S Example I.4.

## What to build

1. Define a representation. Suggested: `Σ n, { l : List Bool // l.length = n ∧ noTwoOnes l }` where `noTwoOnes : List Bool → Prop` says no two adjacent `true`s. Make `noTwoOnes` decidable so `Fintype` works.
2. Build `noConsecOnesClass : CombinatorialClass` with `size = n`.
3. Prove `finite_level`.
4. Sanity `noConsecOnesClass.count n` at `n = 0..6` matching `1, 2, 3, 5, 8, 13, 21`. Use `decide` / `native_decide`.
5. Add a TODO comment for the connection `noConsecOnesClass.count n = Nat.fib (n + 2)` — don't prove unless it's quick and direct.
6. Add to `AnalyticCombinatorics.lean` import list.

## Hard constraints

- Build green.
- No new sorrys (TODO comments fine).
- If the constraint type makes `count` non-trivial to compute (kernel chokes at `n = 5` or `n = 6`), **document the threshold** in the reply and ship whichever sizes work. Don't paper over.
- Reply at HANDOFF/outbox/task-no-two-ones-reply.md.
