# Task — labelCycCount Atom sanity

**File:** `AnalyticCombinatorics/PartA/Ch2/LabelledClass.lean` (append at end, after labelled-CYC theorem)

**Goal:** Compute `labelCycCount Atom n` for small n. labelCycCount Atom n = ∑ k≥1 (labelPow Atom k).count n / k. By labelPow_Atom_count, only k=n contributes giving (n.factorial / n) for n ≥ 1. So labelCycCount Atom n = (n-1)! for n ≥ 1, and 0 for n = 0.

```lean
/-- labelCycCount Atom = (n-1)! for n ≥ 1, 0 for n = 0. -/
example : labelCycCount Atom 0 = 0 := by
  simp [labelCycCount]

example : labelCycCount Atom 1 = 1 := by
  unfold labelCycCount
  simp [labelPow_Atom_count]
  norm_num

-- Add 2, 3, 4 as you can. Each k = n term should give n!/n = (n-1)!.

theorem labelCycCount_Atom_succ (n : ℕ) :
    labelCycCount Atom (n + 1) = (n.factorial : ℚ) := by
  sorry  -- only the k = n+1 summand contributes; (labelPow Atom (n+1)).count (n+1) = (n+1)!
         -- divided by (n+1) gives n!.
```

If the proof is hard, just file the sanity examples and skip the general theorem. Non-essential.

## Hard constraints

- Build green
- No new sorrys (drop the general theorem if needed)
- Reply at HANDOFF/outbox/task-labelled-cyc-sanity-reply.md
