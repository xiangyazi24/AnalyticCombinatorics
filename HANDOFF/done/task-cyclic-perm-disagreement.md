# Task — labelled CYC of posIntClass = ?

**File:** `AnalyticCombinatorics/Examples/SetPartitions.lean` (append at end)

**Goal:** Compute `labelCycCount posIntClass` for small n. Connect to a known sequence.

```lean
example : labelCycCount posIntClass 0 = 0 := by
  unfold CombinatorialClass.labelCycCount
  simp

example : labelCycCount posIntClass 1 = 1 := by
  -- ∑ k ≥ 1, (labelPow posIntClass k).count 1 / k
  -- only k = 1 contributes: posIntClass.count 1 / 1 = 1.
  unfold CombinatorialClass.labelCycCount
  -- Compute by direct evaluation
  sorry  -- if you can land it cleanly without sorry, great; else file a blocker

example : labelCycCount posIntClass 2 = (3/2 : ℚ) := by
  -- k=1: labelPow 1 count 2 / 1 = 1.
  -- k=2: labelPow 2 count 2 / 2 = 2!·S(2,2)/2 = 2/2 = 1.
  -- Sum: 1 + 1 = 2. Hmm, but expected by F&S is 3/2 — let me re-check.
  -- Actually labelCycCount = ∑ count/k where count is unordered? No, it's
  -- the standard CYC formula. Each k-tuple of B-objects contributes
  -- weight 1/k since cyclic rotations are equivalent.
  sorry
```

If the expected values trip up, fall back to: just compute small ones via direct evaluation without expecting them to match a known sequence (the F&S labelled CYC count is not standard combinatorial integer).

## Hard constraints

- Build green
- No new sorrys when delivered (the example sorrys above are placeholders; either fill or drop them)
- Reply at HANDOFF/outbox/task-cyclic-perm-disagreement-reply.md
- File blocker if the sequence doesn't compute nicely
