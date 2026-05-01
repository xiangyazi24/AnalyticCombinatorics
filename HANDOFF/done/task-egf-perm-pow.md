# Task — permClass.egf^k closed form

**File:** `AnalyticCombinatorics/PartA/Ch2/LabelledClass.lean` (append)

**Goal:** Connect `permClass.egf^k` to its coefficient closed form.

```lean
example (k n : ℕ) :
    coeff n (permClass.egf ^ k) = (Nat.multichoose k n : ℚ) := by
  rw [← labelPow_egf]
  rw [coeff_egf]
  rw [labelPow_permClass_count_multichoose]
  push_cast
  field_simp
  ring
```

If the manipulation doesn't close, file blocker.

## Hard constraints

- Build green
- No new sorrys when delivered (or file blocker)
- Reply at HANDOFF/outbox/task-egf-perm-pow-reply.md
