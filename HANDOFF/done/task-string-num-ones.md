# Task — Strings parameter: number of 1s = binomial coefficient

**File:** `AnalyticCombinatorics/Examples/Strings.lean` (append)

**Goal:** Define a parameter on stringClass: `numOnes : List Bool → ℕ` counting `true` letters. Connect joint count to binomial coefficient.

```lean
import AnalyticCombinatorics.PartA.Ch3.Parameters

/-- Parameter: number of `true`s in a binary string. -/
def numOnes : Parameter stringClass := fun (xs : List Bool) => xs.count true

/-- Sanity at small sizes:
    n = 0: 1 string with 0 ones.
    n = 1: 1 string with 0 ones (false), 1 string with 1 one (true).
    n = 2: 1 string with 0 ones (ff,ff), 2 with 1 one (ft, tf), 1 with 2 ones (tt). -/
example : stringClass.jointCount numOnes 0 0 = 1 := by sorry
example : stringClass.jointCount numOnes 1 0 = 1 := by sorry
example : stringClass.jointCount numOnes 1 1 = 1 := by sorry
example : stringClass.jointCount numOnes 2 0 = 1 := by sorry
example : stringClass.jointCount numOnes 2 1 = 2 := by sorry
example : stringClass.jointCount numOnes 2 2 = 1 := by sorry

/-- Joint count is the binomial coefficient: C(n, k). -/
theorem stringClass_jointCount_numOnes (n k : ℕ) :
    stringClass.jointCount numOnes n k = n.choose k := by
  sorry  -- combinatorial bijection
```

If the binomial proof is hard, file blocker — focus on getting at least the small sanity examples (which can be done by `decide` or unfolding `level`).

## Hard constraints

- Build green
- No new sorrys when delivered
- Reply at HANDOFF/outbox/task-string-num-ones-reply.md
- File blocker if the closed form is hard
