# Task — Fubini count via labelSeq satisfies (2 - exp(z)) · F = 1 (partial)

**File:** `AnalyticCombinatorics/Examples/SetPartitions.lean` (append at end)

**Goal:** Show that the EGF of `labelSeq posIntClass` satisfies a recurrence consistent with the closed form `1 / (2 - exp(z))` (the Fubini EGF).

Specifically, since `labelSeq B . egf · (1 - B.egf) = 1` (already proven generally), and `posIntClass.egf = exp(z) - 1` (since count is 1 at every k≥1, count 0 = 0; coeff_k = 1/k! for k≥1, 0 for k=0; sum = exp - 1), we get:

  labelSeq posIntClass . egf · (1 - (exp(z) - 1)) = labelSeq . egf · (2 - exp(z)) = 1.

```lean
/-- posIntClass.egf = exp(z) - 1. -/
theorem posIntClass_egf_eq_exp_sub_one :
    posIntClass.egf = PowerSeries.exp ℚ - 1 := by
  ext n
  rw [CombinatorialClass.coeff_egf]
  rw [show ((PowerSeries.exp ℚ) - 1).coeff n =
        if n = 0 then 0 else (1 / n.factorial : ℚ) from ?_]
  · -- LHS: posIntClass.count n / n! = if n = 0 then 0 else 1/n!.
    by_cases hn : n = 0
    · subst hn
      rw [posIntClass.count_zero]
      simp
    · rw [posIntClass.count_pos (Nat.pos_of_ne_zero hn)]
      simp
  · -- aux: coeff of (exp - 1) at n = 1/n! - δ_{n,0}
    rw [map_sub, PowerSeries.coeff_exp, PowerSeries.coeff_one]
    by_cases hn : n = 0
    · subst hn; simp
    · simp [hn]

/-- The Fubini EGF satisfies (2 - exp(z)) · F = 1. -/
theorem labelSeq_posIntClass_egf_mul_two_sub_exp :
    (CombinatorialClass.labelSeq posIntClass posIntClass.count_zero).egf
      * (2 - PowerSeries.exp ℚ) = 1 := by
  have h := CombinatorialClass.labelSeq_egf_mul_one_sub_egf posIntClass posIntClass.count_zero
  rw [posIntClass_egf_eq_exp_sub_one] at h
  -- h : (1 - (exp - 1)) * labelSeq.egf = 1
  -- = (2 - exp) * labelSeq.egf = 1, then commute mul
  rw [show (1 - (PowerSeries.exp ℚ - 1) : PowerSeries ℚ) = 2 - PowerSeries.exp ℚ from by ring] at h
  rw [mul_comm]
  exact h
```

If the proof breaks at intermediate steps, adapt — the key chain is:
1. posIntClass.egf = exp - 1 (via coeff comparison)
2. labelSeq.egf · (1 - posIntClass.egf) = 1 (already have)
3. Substitute (1) into (2) and rearrange to get (2 - exp) · labelSeq.egf = 1.

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-fubini-direct-reply.md
