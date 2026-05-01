# Task — compositionClass parts vs sum bivariate sanity

**File:** `AnalyticCombinatorics/Examples/Compositions.lean` (append)

```lean
example : compositionClass.jointCount numParts 3 1 = 1 := by sorry  -- only [3]
example : compositionClass.jointCount numParts 3 2 = 2 := by sorry  -- [1,2], [2,1]
example : compositionClass.jointCount numParts 3 3 = 1 := by sorry  -- [1,1,1]
```

If sanity computations get blocked, file blocker.

## Hard constraints

- Build green
- No new sorrys when delivered (or file blocker)
- Reply at HANDOFF/outbox/task-comp-bivariate-reply.md
