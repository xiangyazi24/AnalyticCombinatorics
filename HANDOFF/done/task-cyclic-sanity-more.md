# Task — cyclic perm sanity 6, 7, 8

**File:** `AnalyticCombinatorics/Examples/CyclicPermutations.lean` (append)

```lean
example : labelCycCount Atom 6 = 120 := labelCycCount_Atom_succ 5  -- 5! = 120
example : labelCycCount Atom 7 = 720 := labelCycCount_Atom_succ 6  -- 6! = 720
example : labelCycCount Atom 8 = 5040 := labelCycCount_Atom_succ 7  -- 7! = 5040
```

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-cyclic-sanity-more-reply.md
