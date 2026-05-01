# Task — full Pascal-row sanity for stringNumTrue

**File:** `AnalyticCombinatorics/Examples/Strings.lean` (append)

The file already has stringNumTrue Parameter and a few joint-count sanity examples. Add the **complete** rows:

```lean
example : stringClass.jointCount stringNumTrue 5 0 = 1 := by ...
example : stringClass.jointCount stringNumTrue 5 1 = 5 := by ...
example : stringClass.jointCount stringNumTrue 5 2 = 10 := by ...
example : stringClass.jointCount stringNumTrue 5 3 = 10 := by ...
example : stringClass.jointCount stringNumTrue 5 4 = 5 := by ...
example : stringClass.jointCount stringNumTrue 5 5 = 1 := by ...
```

And similarly for `n = 6`: `1, 6, 15, 20, 15, 6, 1`.

Use whatever tactic the existing examples use.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-string-pascal-reply.md.
