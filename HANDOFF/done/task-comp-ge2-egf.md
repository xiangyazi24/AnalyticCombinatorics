# Task — compositionGe2Class basic identities

**File:** `AnalyticCombinatorics/Examples/Compositions.lean` (append)

**Goal:** Add a basic identity and small sanity checks for `compositionGe2Class`.

```lean
/-- count 0 = 1 (only empty composition has total 0). -/
example : compositionGe2Class.count 0 = 1 := by
  show (CombinatorialClass.seqClass posIntGe2Class _).count 0 = 1
  rw [CombinatorialClass.seqClass.count_zero]

/-- count 1 = 0 (no part of size 1, so no composition of total 1). -/
example : compositionGe2Class.count 1 = 0 := by
  show (CombinatorialClass.seqClass posIntGe2Class _).count 1 = 0
  rw [CombinatorialClass.seqClass.count_succ]
  -- ∑ p ∈ antidiag 1, posIntGe2.count p.1 · count p.2
  -- p ∈ {(0,1), (1,0)}: count 0 = 0, count 1 = 0 (no parts of size 1).
  sorry  -- if simp/decide doesn't close, file blocker
```

If sanity checks are involved, file blocker — main payoff is the count_zero example.

## Hard constraints

- Build green
- No new sorrys when delivered (or file blocker)
- Reply at HANDOFF/outbox/task-comp-ge2-egf-reply.md
