# Task — composition EGF coefficient (rational form via factorial)

**File:** `AnalyticCombinatorics/Examples/Compositions.lean` (append at end)

**Goal:** Add the rational EGF coefficient form for compositionClass.

```lean
/-- EGF coefficient: [zⁿ] compositionClass.egf = compositionClass.count n / n!
    = 2^(n-1) / n! for n ≥ 1, 1 for n = 0. -/
example : compositionClass.egf.coeff 0 = 1 := by
  rw [CombinatorialClass.coeff_egf, compositionClass_count_zero]
  simp

example (n : ℕ) (hn : 1 ≤ n) :
    compositionClass.egf.coeff n = (2 ^ (n - 1) : ℚ) / n.factorial := by
  rw [CombinatorialClass.coeff_egf, compositionClass_count_eq_pow_pred n hn]
  push_cast
  rfl
```

If unification trips on `coeff` namespace, use `PowerSeries.coeff` or full path.

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-comp-egf-extras-reply.md
