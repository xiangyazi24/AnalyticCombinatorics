# Task — fibClass numParts parameter

**File:** `AnalyticCombinatorics/Examples/Fibonacci.lean` (append)

**Goal:** Define numParts on fibClass and prove a small property.

```lean
import AnalyticCombinatorics.PartA.Ch3.Parameters

/-- Number of parts in a fibClass composition. -/
def fibNumParts : Parameter fibClass := List.length

/-- Sanity: small jointCount values. -/
example : fibClass.jointCount fibNumParts 0 0 = 1 := by sorry
example : fibClass.jointCount fibNumParts 1 1 = 1 := by sorry
example : fibClass.jointCount fibNumParts 2 1 = 1 := by sorry  -- only [2]
example : fibClass.jointCount fibNumParts 2 2 = 1 := by sorry  -- only [1,1]
```

If proofs are involved, file blocker.

## Hard constraints

- Build green, no new sorrys (or file blocker)
- Reply at HANDOFF/outbox/task-fib-num-parts-reply.md
