# Task — Compositions extra sanity + closed form

**File:** `AnalyticCombinatorics/Examples/Compositions.lean` (append at end)

**Goal:** Add more sanity checks for `compositionClass.count` and a closed-form result.

```lean
example : compositionClass.count 3 = 4 := compositionClass_count_succ 2
example : compositionClass.count 5 = 16 := compositionClass_count_succ 4
example : compositionClass.count 6 = 32 := compositionClass_count_succ 5
example : compositionClass.count 7 = 64 := compositionClass_count_succ 6

/-- Closed form for n ≥ 1: count of compositions of n equals 2^(n-1). -/
theorem compositionClass_count_eq_pow_pred (n : ℕ) (hn : 1 ≤ n) :
    compositionClass.count n = 2 ^ (n - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [compositionClass_count_succ]
  congr 1; omega
```

If the `obtain` form needs adjustment for the index shift, use `Nat.exists_eq_succ_of_ne_zero` or just `cases n`.

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-comp-sanity-reply.md
