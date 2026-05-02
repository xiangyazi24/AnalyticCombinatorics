# Task — Schröder sanity beyond k=18

**File:** `AnalyticCombinatorics/Examples/SchroderTrees.lean` (append)

The file has `largeSchroderNumber k` sanity through k=18 (600318853926). Extend through k=21.

Large Schröder numbers: S(19)=3236724317468, S(20)=17518619320890, S(21)=95149655201962.

Use the same proof shape: `example : largeSchroderNumber k = val := by decide`

If `decide` times out at some k, try `native_decide`. Document threshold if needed.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-schr-extras6-reply.md.
- **ONLY modify `AnalyticCombinatorics/Examples/SchroderTrees.lean`.** Local instances if needed.
