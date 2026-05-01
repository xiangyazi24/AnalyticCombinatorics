# Task — Derangement EGF coefficient form

**File:** `AnalyticCombinatorics/Examples/Derangements.lean` (append)

**Goal:** Direct EGF coefficient form for derangementClass.

```lean
example (n : ℕ) :
    derangementClass.egf.coeff n = (Nat.numDerangements n : ℚ) / n.factorial := by
  rw [CombinatorialClass.coeff_egf]
  rw [show (derangementClass.count n : ℕ) = Nat.numDerangements n from
        derangementClass_count_eq_numDerangements n]
```

Use whichever name `Nat.numDerangements` resolves to in this build (codex earlier added a bridge).

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-derangement-egf-coeff-reply.md
