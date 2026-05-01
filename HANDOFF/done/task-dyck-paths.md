# Task — Dyck paths example file

**File:** `AnalyticCombinatorics/Examples/DyckPaths.lean` (NEW)

A Dyck path of length `2n` is a lattice path with steps `U = (1, 1)` and `D = (1, -1)` that starts at `(0, 0)`, ends at `(2n, 0)`, and never goes below the x-axis. Equivalently: a list of `Bool`s of length `2n` (interpret `true = U`, `false = D`) such that every prefix has `#U ≥ #D` and total `#U = #D = n`.

The number of Dyck paths of length `2n` is `Catalan(n)`. F&S Example I.6.

## What to build

1. Define a representation `DyckPath` (e.g. `Σ n, { l : List Bool // l.length = 2 * n ∧ valid l }` where `valid` checks the prefix condition; or use Mathlib's `DyckWord` / `Nat.Catalan` infrastructure if it exists — search the build path).
2. Build `dyckPathClass : CombinatorialClass` with `size = n` (paths of half-length `n`).
3. Sanity examples `dyckPathClass.count n = Nat.catalan n` for `n = 0..5` (`1, 1, 2, 5, 14, 42`). Use `decide` / `native_decide`.
4. Add an OGF-quadratic TODO comment (`D(z) = 1 + z·D(z)²`) — don't prove.
5. Add to `AnalyticCombinatorics.lean`'s top-level imports if such an aggregate file exists.

## Hard constraints

- Build green.
- No new sorrys (TODOs as comments are fine).
- If Mathlib's `DyckWord` API doesn't fit `CombinatorialClass.count` shape cleanly, document the impedance mismatch and **stop** — we'll revisit. Don't force it.
- Reply at HANDOFF/outbox/task-dyck-paths-reply.md.
- Match the existing `Examples/*.lean` style (see e.g. `Examples/BinaryTrees.lean`, `Examples/PlaneTrees.lean`).
