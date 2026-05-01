# Task — Compositions: number of parts parameter

**File:** `AnalyticCombinatorics/Examples/Compositions.lean` (append)

**Goal:** Define `numParts : List _ → ℕ = List.length` parameter on compositionClass and add a sanity example.

```lean
import AnalyticCombinatorics.PartA.Ch3.Parameters

/-- Number of parts of a composition (= list length). -/
def numParts : Parameter compositionClass := List.length

/-- Sanity at small n: count compositions of n with exactly k parts. -/
example : compositionClass.jointCount numParts 0 0 = 1 := by sorry
example : compositionClass.jointCount numParts 1 1 = 1 := by sorry  -- only [1]
example : compositionClass.jointCount numParts 2 1 = 1 := by sorry  -- only [2]
example : compositionClass.jointCount numParts 2 2 = 1 := by sorry  -- only [1,1]
```

If proving these is hard via `decide`, file blocker — they need direct evaluation
of the level Finset.

## Hard constraints

- Build green
- No new sorrys when delivered (or file blocker)
- Reply at HANDOFF/outbox/task-comp-num-parts-reply.md
