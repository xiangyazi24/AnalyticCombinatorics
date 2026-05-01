# Task — Multivariate generating function scaffold (Ch III opener)

**File:** `AnalyticCombinatorics/PartA/Ch3/Parameters.lean` (new). Add to root.

**Goal:** Start Chapter III by defining a basic `combinatorial parameter` and the bivariate generating function tracking `(size, parameter)`.

```lean
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.MvPowerSeries.Basic
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass

open PowerSeries CombinatorialClass

/-! # Ch III — Combinatorial Parameters and Multivariate Generating Functions
    F&S Chapter III. -/

/-- A combinatorial parameter on `A` is a function `χ : A.Obj → ℕ`. -/
abbrev Parameter (A : CombinatorialClass) : Type _ := A.Obj → ℕ

namespace CombinatorialClass

/-- Joint count: number of objects of size `n` with parameter value `k`. -/
noncomputable def jointCount (A : CombinatorialClass) (χ : Parameter A) (n k : ℕ) : ℕ :=
  ((A.level n).filter (fun a => χ a = k)).card

/-- Sanity: summing over all k recovers the size-only count. -/
theorem jointCount_sum_eq_count
    (A : CombinatorialClass) (χ : Parameter A) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), A.jointCount χ n k +
    ∑ k ∈ (Finset.range (n + 1))ᶜ, A.jointCount χ n k = A.count n := by
  sorry  -- needs care with filtering and sum partitioning
```

Just the skeleton — the cleanest thing is to define `jointCount` and a basic identity. Skip multivariate power series for now (just have integer counts).

Bonus if cheap: prove `jointCount ≤ A.count` (each filter is a subset).

If anything is too complex, file simpler scaffold and document blockers.

## Hard constraints

- Build green
- No new sorrys when delivered (file blocker if scaffolding hits issues)
- Add new file to AnalyticCombinatorics.lean root imports
- Reply at HANDOFF/outbox/task-mvpower-scaffold-reply.md
