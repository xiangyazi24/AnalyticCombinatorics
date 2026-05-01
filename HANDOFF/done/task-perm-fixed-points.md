# Task — permClass fixed-point parameter

**File:** `AnalyticCombinatorics/PartA/Ch2/LabelledClass.lean` (append)

**Goal:** Define a `numFixedPoints` parameter on permClass.

```lean
import AnalyticCombinatorics.PartA.Ch3.Parameters

/-- For (n, σ) ∈ permClass, the number of fixed points of σ. -/
noncomputable def permClass.numFixedPoints :
    Parameter permClass :=
  fun s => (Finset.univ.filter (fun i : Fin s.fst => s.snd i = i)).card

/-- Sanity: count permClass.jointCount numFixedPoints n n = 1
    (only the identity has all n fixed points; for n = 0 the empty
    permutation vacuously has 0 fixed points so 0 = n). -/
example : permClass.jointCount permClass.numFixedPoints 0 0 = 1 := by sorry
example : permClass.jointCount permClass.numFixedPoints 1 1 = 1 := by sorry
```

If proofs are tricky, file blocker — main payoff is having the parameter defined.

## Hard constraints

- Build green
- No new sorrys when delivered (file blocker if hard)
- Reply at HANDOFF/outbox/task-perm-fixed-points-reply.md
