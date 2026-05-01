# Task — derangement EGF explicit form D(X) = exp(-X)/(1-X)

**File:** `AnalyticCombinatorics/Examples/Derangements.lean` (append)

**Goal:** Pull out the intermediate identity (1-X)·D(X) = exp(-X) which is implicit in the previous proof.

```lean
example :
    (1 - PowerSeries.X) * derangementClass.egf =
      PowerSeries.exp (R := ℚ) ∘ PowerSeries.scaleLeft (-1) := by
  sorry  -- adapt to whatever exp(-X) form Mathlib has
```

If Mathlib's exp(-X) is awkward to express, file blocker — main payoff is documenting that the intermediate exists.

## Hard constraints

- Build green
- No new sorrys when delivered (or file blocker)
- Reply at HANDOFF/outbox/task-derangement-egf-explicit-reply.md
