# Task — Stirling 2nd kind bridge to labelPow posIntClass

**File:** `AnalyticCombinatorics/Examples/SetPartitions.lean` (append at end)

**Goal:** Establish the formal bridge between our framework and Mathlib's Stirling numbers of the 2nd kind. Specifically:

```
(labelPow posIntClass k).count n = k! · S(n, k)
```

where S is Mathlib's `stirling2 n k` (Stirling number of the 2nd kind from
`Mathlib.Combinatorics.Enumerative.Stirling`).

If Mathlib's Stirling API doesn't expose this exactly, choose the closest
identifier and document any naming bridge.

```lean
import Mathlib.Combinatorics.Enumerative.Stirling

/-- Stirling 2nd kind connection: ordered set partitions of {1..n} into k blocks. -/
theorem labelPow_posIntClass_count_eq_factorial_mul_stirling (n k : ℕ) :
    (CombinatorialClass.labelPow posIntClass k).count n =
      k.factorial * (Nat.stirling2 n k) := by
  sorry  -- by induction on k, matching the Stirling recurrence
         -- against the labelPow recurrence
```

If Mathlib's `stirling2` definition differs from F&S/Bell-compatible
convention, document and adapt.

If this proof is hard, file blocker with details — the result is non-essential
since we already have `labelSetCount_posIntClass_eq_bell` via the ODE route.

## Hard constraints

- Build green; `lake build`
- No new sorrys when delivered (or file blocker)
- Reply at HANDOFF/outbox/task-stirling-bridge-reply.md
