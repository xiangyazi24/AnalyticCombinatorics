# Task — perm = ε ⋆ id permutations relation (or a similar structural id)

**File:** `AnalyticCombinatorics/PartA/Ch2/LabelledClass.lean` (append at end)

**Goal:** Add a few small structural EGF identities involving permClass.

```lean
/-- permClass.egf · (1 - X) = 1 (already proven as permClass_egf_mul_one_sub_X). 
    Add a corollary: Atom + permClass labelProd EGF identity. -/

/-- Labelled product of Atom and permClass: EGF = X · (1-X)⁻¹ = X / (1-X). -/
theorem permClass_labelProd_Atom_egf :
    (permClass.labelProd Atom).egf * (1 - PowerSeries.X) = PowerSeries.X := by
  rw [labelProd_egf, mul_assoc, ← labelProd_egf]
  -- (permClass.egf * Atom.egf) * (1 - X) = permClass.egf * (Atom.egf * (1 - X))
  rw [Atom_egf]
  -- permClass.egf * X * (1 - X) = X
  rw [show permClass.egf * PowerSeries.X * (1 - PowerSeries.X)
      = PowerSeries.X * (permClass.egf * (1 - PowerSeries.X)) by ring,
      permClass_egf_mul_one_sub_X, mul_one]
```

If the rewrite chain doesn't quite line up, adapt — the key insight is `permClass.egf · (1-X) = 1` (already proven) and `Atom.egf = X`.

Bonus: also try

```lean
/-- (permClass).egf has constant term 1 (since count 0 = 0! = 1). -/
example : (PowerSeries.constantCoeff ℚ) permClass.egf = 1 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff.symm, permClass_egf_coeff]
```

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-perm-disjoint-deduce-reply.md
