# Task — IntegerPartitions example file

**File:** `AnalyticCombinatorics/Examples/IntegerPartitions.lean` (NEW)

Create a new example file for integer partitions in the symbolic-method style we've been using. F&S Section I.3.

## What to build

1. A `CombinatorialClass` instance `intPartitionClass` whose objects are integer partitions of `n` for some `n`, and whose `size` is `n`. Use `Nat.Partition` from Mathlib if it exists (search the build for `Nat.Partition`); otherwise pick a simple representative type (e.g. `{ l : List ℕ // l.Sorted (· ≥ ·) ∧ ∀ k ∈ l, 0 < k }` with size = `l.sum`).
2. Prove `intPartitionClass.finite_level n` (i.e. only finitely many partitions of any given `n`).
3. Sanity: `intPartitionClass.count n = ` partition count for `n = 0..6`. Values: `1, 1, 2, 3, 5, 7, 11`.
4. (Optional, only if time permits) state the OGF identity `intPartitionClass.ogf = ∏_{k ≥ 1} (1 - z^k)⁻¹` as a comment / TODO. Don't prove it — that's substantial.

## Hard constraints

- Build green.
- No new sorrys (anything aspirational stays as a `-- TODO:` comment, not a sorry).
- The Mathlib bridge is the bottleneck — read `import Mathlib.Combinatorics.Partition` first to see what's available before picking a representation.
- Reply at HANDOFF/outbox/task-integer-partitions-reply.md.
- If the Mathlib `Nat.Partition` API doesn't fit the existing `CombinatorialClass` shape cleanly, **document the impedance mismatch** instead of forcing a bad fit; we can come back with a different rep.

## Style

- Match the existing `Examples/*.lean` style (see e.g. `Examples/Compositions.lean`).
- Add to `AnalyticCombinatorics.lean` import list at the top level if there is one (check the existing files).
