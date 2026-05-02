# Task: Involutions (Ch II)

## Goal

Create `AnalyticCombinatorics/PartA/Ch2/Involutions.lean`.

## What to formalize

Involutions are permutations that are their own inverse (only fixed points and transpositions).

1. `involutionCount : ℕ → ℕ` via recursion:
   - involutionCount 0 = 1
   - involutionCount 1 = 1  
   - involutionCount (n+2) = involutionCount (n+1) + (n+1) * involutionCount n

2. Sanity checks (native_decide): 1, 1, 2, 4, 10, 26, 76

3. The recursion as a standalone theorem.

4. EGF statement (just the Prop, don't prove): EGF = exp(z + z²/2)

## Imports

```lean
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic
```

## Constraints

- Must compile: `lake build AnalyticCombinatorics.PartA.Ch2.Involutions`
- No sorry, no axiom
- Delete anything that doesn't compile
- Keep it simple: recursion + native_decide sanity

## Output

Write file, verify build, report.
