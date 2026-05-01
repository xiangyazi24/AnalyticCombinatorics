# Task — Compositions extras (count_two_pow recursion + ogf coeff form)

**File:** `AnalyticCombinatorics/Examples/Compositions.lean` (append at end)

**Goal:** Add a few more compositional identities.

```lean
/-- The OGF of compositions has coefficient 2^(n-1) for n ≥ 1 over ℤ. -/
theorem compositionClass_ogfZ_coeff_pos (n : ℕ) (hn : 1 ≤ n) :
    PowerSeries.coeff n (ogfZ compositionClass) = (2 ^ (n - 1) : ℤ) := by
  unfold ogfZ
  rw [PowerSeries.coeff_map]
  rw [coeff_ogf]
  rw [compositionClass_count_eq_pow_pred n hn]
  push_cast
  rfl

/-- Sum identity: 2 · count(n+1) = count(n+2). Linear recurrence. -/
example (n : ℕ) :
    2 * compositionClass.count (n + 1) = compositionClass.count (n + 2) := by
  rw [compositionClass_count_succ, compositionClass_count_succ, pow_succ]
  ring
```

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-comp-extras-reply.md
