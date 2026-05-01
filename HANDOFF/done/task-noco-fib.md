# Task — Connect StringsNoConsecutiveOnes to Fibonacci

**File:** `AnalyticCombinatorics/Examples/StringsNoConsecutiveOnes.lean` (append)

The file has a TODO: `noConsecOnesClass.count n = Nat.fib (n + 2)`. Try to **prove** it.

## Suggested approach

Direct induction with the standard split:

- For length-`n` strings with no two consecutive `true`s, condition on the first bit:
  - if first bit = `false`, the rest is any length-`(n-1)` such string → `count(n-1)` ways.
  - if first bit = `true`, the second bit must be `false`, and the rest is any length-`(n-2)` such string → `count(n-2)` ways.

So `count(n+2) = count(n+1) + count(n)`, with `count(0) = 1` and `count(1) = 2`. That matches `Nat.fib (n + 2)` (since `fib 2 = 1, fib 3 = 2`, so `fib(n+2)` gives `1, 2, 3, 5, 8, ...`).

You may need a `Finset.card_bij` between `count(n+2)` and the disjoint union `count(n+1) ⊕ count(n)`. Or: define a recursive count function on `ℕ` (matching the constraint shape), prove it equals `Fintype.card`, then prove it equals `Nat.fib (n+2)` by `Nat.fib_add_two` style induction.

## Hard constraints

- Build green.
- No new sorrys (if the bijective recurrence is too painful, **document a blocker** and stop — don't paper over).
- Reply at HANDOFF/outbox/task-noco-fib-reply.md.
- This is a real proof, not just sanity. Allow yourself to spend some compute on it.
- If the recurrence step proves stubborn, fall back to: prove the recurrence on a recursive `ℕ → ℕ` count function, leave the bridge to `Fintype.card` as a TODO, and document.
