# Task — CompositionsEven closed-form theorems

**File:** `AnalyticCombinatorics/Examples/CompositionsEven.lean` (append)

The file has sanity at `n = 0..10`. Try the closed forms:

```lean
theorem evenCompClass_count_odd (k : ℕ) :
    evenCompClass.count (2 * k + 1) = 0 := by
  sorry

theorem evenCompClass_count_even_succ (k : ℕ) :
    evenCompClass.count (2 * (k + 1)) = 2 ^ k := by
  sorry
```

(With `count 0 = 1` already direct.)

## Suggested approach

`evenCompClass = seqClass evenPartClass _`. A composition of `n` into even positive parts has each part ≥ 2 even. For odd `n`, no decomposition works (sum of evens is even). For `n = 2(k+1)`, there's a bijection with `compositionClass.count (k+1) = 2^k` (the standard composition count), by halving each part.

The bijection: `[2a_1, 2a_2, ..., 2a_m]` with `∑ a_i = k+1` ↔ `[a_1, ..., a_m]` with `∑ a_i = k+1, all a_i ≥ 1`. The latter is exactly `compositionClass.count (k+1)`.

If the existing `compositionClass_count_eq_pow` (from `Examples/Compositions.lean`) is accessible, use it. Otherwise the explicit formula `compositionClass.count (k+1) = 2^k` should be in that file.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-even-comp-closed-reply.md.
- If the bijection between even-compositions of `2(k+1)` and compositions of `k+1` is heavy in Lean, document and ship just the odd case (which is easier — sum of evens is even, parity contradiction).
- Do NOT introduce axioms.
