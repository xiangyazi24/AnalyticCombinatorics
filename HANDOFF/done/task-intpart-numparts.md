# Task — IntegerPartitions bivariate by number of parts

**File:** `AnalyticCombinatorics/Examples/IntegerPartitions.lean` (append)

The file builds `intPartitionClass` (uses Mathlib's `Nat.Partition n`). Add a `Parameter` recording the number of parts, plus small bivariate sanity.

## What to add

1. `intPartNumParts : Parameter intPartitionClass` returning the number of parts of the partition. Use whatever Mathlib helper exists on `Nat.Partition` (look for `Nat.Partition.parts.card` or `Multiset.card p.parts`); if that lookup is awkward, define inline with `(p.parts).card`.

2. Sanity examples: `intPartitionClass.jointCount intPartNumParts n k = ?` for small `(n, k)`. E.g.:

   - `(4, 1) = 1`  (just `[4]`)
   - `(4, 2) = 2`  (`[3,1]`, `[2,2]`)
   - `(4, 3) = 1`  (`[2,1,1]`)
   - `(4, 4) = 1`  (`[1,1,1,1]`)
   - `(5, 2) = 2`  (`[4,1]`, `[3,2]`)
   - `(5, 3) = 2`  (`[3,1,1]`, `[2,2,1]`)

   Use `decide` / `native_decide`. If the bridge to `Nat.Partition.parts.card` is heavy, switch tactic.

3. (Optional) Sum identity: `∑ k, jointCount n k = p_n` for some small n (e.g. `n = 4`, sum should equal `5`).

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-intpart-numparts-reply.md.
- If the parameter definition forces a non-trivial proof obligation (e.g. `DecidableEq` on `Nat.Partition`), stop and document — we can revisit. Don't introduce ad-hoc instances.
