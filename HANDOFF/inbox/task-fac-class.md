# Task — `factorialClass` count

**File:** `AnalyticCombinatorics/PartA/Ch2/LabelledClass.lean` (append) or new file `AnalyticCombinatorics/Examples/Permutations.lean`.

**Goal:** Sanity-check the EGF differential identity `permClass.egf = (1 - X)⁻¹` by extracting concrete factorials from Mathlib's `centralBinom`-like identities, OR prove additional structural identities about permClass.

A simple deliverable: prove that `permClass.egf · (1 - PowerSeries.X)^k = 1 - ∑ ... ` for small k as a sanity check, OR connect:

```lean
example : permClass.count 5 = 120 := by rw [permClass_count_eq_factorial]; rfl
example : permClass.count 6 = 720 := by rw [permClass_count_eq_factorial]; rfl
example : permClass.count 7 = 5040 := by rw [permClass_count_eq_factorial]; rfl

/-- Sanity examples for permClass via the EGF coefficient identity. -/
example : (PowerSeries.coeff 0 permClass.egf : ℚ) = 1 := permClass_egf_coeff 0
example : (PowerSeries.coeff 5 permClass.egf : ℚ) = 1 := permClass_egf_coeff 5
```

If you can land additional structural examples (e.g., labelSetCount permClass n
or labelProdCount permClass permClass n), bonus.

## Hard constraints

- `lake build` green
- No new sorrys
- Write reply file at HANDOFF/outbox/task-fac-class-reply.md
