# Task — string OGF coeff closed form

**File:** `AnalyticCombinatorics/Examples/Strings.lean` (append at end)

**Goal:** Add the closed-form coefficient identity for stringClass.ogfZ.

```lean
/-- Direct coefficient form: [zⁿ] stringClass.ogfZ = 2^n. -/
theorem stringClass_ogfZ_coeff (n : ℕ) :
    PowerSeries.coeff n (ogfZ stringClass) = (2 ^ n : ℤ) := by
  unfold ogfZ
  rw [PowerSeries.coeff_map, coeff_ogf, stringClass_count_eq_pow]
  push_cast
  rfl
```

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-string-ogf-coeff-reply.md
