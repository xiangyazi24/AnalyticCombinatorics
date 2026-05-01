# Task — Bell EGF identity (1 - exp(exp(z)-1))-style

**File:** `AnalyticCombinatorics/Examples/SetPartitions.lean` (append)

**Goal:** Document the relationship `bellSeries · (1 - posIntClass.egf) ?` etc, parallel to Fubini.

The Bell numbers' EGF is `exp(exp(z) - 1)`. We have `posIntClass.egf = exp(z) - 1` and `labelSetSeries posIntClass` (the Bell EGF) satisfies the Bell ODE.

```lean
/-- Sanity: the Bell EGF coefficient at n equals (Bell n : ℚ) / n!. 
    Already implicit in labelSetCount_posIntClass_eq_bell. -/
example (n : ℕ) :
    coeff n (CombinatorialClass.labelSetCount posIntClass · ↑n.factorial⁻¹) = ?_ :=
  sorry  -- adapt or remove as needed

/-- Bell ODE (already proven internally to bell-numbers task):
    (labelSetSeries posIntClass)' = exp(z) · (labelSetSeries posIntClass).
    Equivalently: posIntClass.egf' · (labelSetSeries) = exp · labelSetSeries — adapt as needed. -/
```

If the existing proof of `labelSetCount_posIntClass_eq_bell` already exposes `labelSetSeries` and `bellSeries`, just rename or document them; otherwise file blocker.

## Hard constraints

- Build green
- No new sorrys when delivered
- Reply at HANDOFF/outbox/task-bell-egf-reply.md
- File blocker if the ODE doesn't expose cleanly
