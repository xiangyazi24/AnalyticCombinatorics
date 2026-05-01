# Task — Compositions into odd parts count = Nat.fib (n+1)

**File:** `AnalyticCombinatorics/Examples/CompositionsOdd.lean` (append)

The file has TODO `oddCompClass.count n = Nat.fib (n + 1)`. Try to **prove**:

```lean
theorem oddCompClass_count_eq_fib (n : ℕ) :
    oddCompClass.count n = Nat.fib (n + 1) := by
  sorry
```

## Suggested approach (recurrence)

Establish:
- `oddCompClass.count 0 = 1`  (empty composition)
- `oddCompClass.count 1 = 1`  (`[1]`)
- `oddCompClass.count (n+2) = oddCompClass.count (n+1) + oddCompClass.count n` (combinatorial recurrence)

Then `Nat.twoStepInduction` finishes since `Nat.fib` satisfies the same recurrence with same seeds (`fib 1 = 1, fib 2 = 1, fib (n+3) = fib (n+2) + fib (n+1)`).

The recurrence step needs a bijection: compositions of `n+2` into odd parts split into:
- those with first part `1` ↔ odd compositions of `n+1`
- those with first part `≥ 3` ↔ odd compositions of `n` (subtract 2 from first part; result still odd, still positive)

You may be able to lean on the existing `seqClass` machinery (`seqClass_ogf_recursion`?) for half of this.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-odd-comp-fib-reply.md.
- If the bijection becomes too painful, document the blocker. Don't paper over with axioms.
- Look at how `Examples/StringsNoConsecutiveOnes.lean` did its first-bit-split bijection — that file just landed `count = Nat.fib (n+2)` via `Nat.twoStepInduction`; the structure of this proof should be similar.
