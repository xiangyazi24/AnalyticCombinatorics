# Task — Permutations vs derangements EGF connection

**File:** `AnalyticCombinatorics/Examples/Derangements.lean` (append)

**Goal:** Document the classical EGF identity D(z) · exp(z) = 1/(1-z) i.e., derangementClass.egf · exp(z) = permClass.egf in coefficient terms.

```lean
/-- Coefficient identity: numDerangements convolution with 1/k! gives n! / n!. -/
example (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
      (Nat.numDerangements (n - k) : ℚ) / (n - k).factorial / k.factorial = 1 := by
  sorry  -- if Mathlib has this directly, use it; else file blocker
```

If too involved, file blocker — main payoff is documenting the identity.

## Hard constraints

- Build green
- No new sorrys when delivered (or file blocker)
- Reply at HANDOFF/outbox/task-egf-perm-derangement-reply.md
