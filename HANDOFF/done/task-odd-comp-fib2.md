# Task — Compositions into odd parts: corrected Fibonacci closed form

**File:** `AnalyticCombinatorics/Examples/CompositionsOdd.lean` (append)

(Previous attempt was blocked because I gave the wrong shift. Codex correctly diagnosed: the count sequence is `1, 1, 1, 2, 3, 5, 8, 13, ...` and matches `Nat.fib n` only for `n ≥ 1` (with `count 0 = 1` while `fib 0 = 0`).)

## What to prove

Prove the corrected closed form:

```lean
theorem oddCompClass_count_succ_eq_fib (n : ℕ) :
    oddCompClass.count (n + 1) = Nat.fib (n + 1) := by
  sorry
```

This shifts the index so that we avoid the awkward `n = 0` case (`fib 0 = 0` mismatch).

Verify:
- `n = 0`: `count 1 = 1 = fib 1` ✓
- `n = 1`: `count 2 = 1 = fib 2` ✓
- `n = 2`: `count 3 = 2 = fib 3` ✓
- `n = 3`: `count 4 = 3 = fib 4` ✓

## Suggested approach

The combinatorial recurrence holds **for `n ≥ 3`** (i.e., `count (n+3) = count (n+2) + count (n+1)`), since the bijection (first part = 1 vs first part ≥ 3) only makes sense when the smaller composition class is non-degenerate.

So:
1. Prove `count (n+3) = count (n+2) + count (n+1)` for all `n` by combinatorial bijection.
2. Use `Nat.twoStepInduction` (or equivalent) starting from seeds `count 1 = 1, count 2 = 1`.
3. Conclude `count (n+1) = Nat.fib (n+1)` since `Nat.fib` satisfies the same recurrence with the same seeds.

Or:
- Lean on Mathlib's `Nat.fib_add_two` directly: `fib (n+3) = fib (n+2) + fib (n+1)`.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-odd-comp-fib2-reply.md.
- The combinatorial recurrence step is the load-bearing piece. If it gets painful, document and ship just the recurrence as a standalone lemma without the closed form.
- Do NOT introduce axioms.
- Look at `Examples/StringsNoConsecutiveOnes.lean`'s `noConsecOnesClass_count_eq_fib` for a template.
