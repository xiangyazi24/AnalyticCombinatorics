# Task — Schröder numbers (large) example

**File:** `AnalyticCombinatorics/Examples/SchroderTrees.lean` (new). Add to root.

**Goal:** Define Schröder trees (each node either leaf or has ≥ 2 children) — count = large Schröder numbers OEIS A006318: 1, 2, 6, 22, 90, 394.

```lean
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass

/-- Schröder tree: leaf, or internal node with a list of ≥ 2 children. -/
inductive SchroderTree : Type
  | leaf : SchroderTree
  | node : (children : List SchroderTree) → 2 ≤ children.length → SchroderTree

namespace SchroderTree

/-- Size = number of leaves - 1 (= number of internal nodes for binary
    case; for k-ary nodes it's the standard "Schröder size" convention).
    Adjust as needed; if simpler definitions exist in the F&S literature
    use the standard one. -/
def size : SchroderTree → ℕ
  | leaf => 0
  | node children _ => 1 + (children.map size).sum

end SchroderTree
```

If the inductive form with the proof argument is awkward, use a quotient or filter approach. File blocker if structurally difficult.

## Hard constraints

- Build green
- No new sorrys when delivered (or file blocker)
- Add to root imports
- Reply at HANDOFF/outbox/task-schroder-reply.md
