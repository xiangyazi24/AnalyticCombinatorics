# Task: Schröder Trees OGF Theory

## Goal

Create `AnalyticCombinatorics/PartA/Ch1/SchroederTheory.lean` connecting Schröder numbers to the OGF framework.

## What to formalize

Large Schröder numbers count plane trees where internal nodes have ≥ 2 children. Alternatively, they count lattice paths from (0,0) to (n,n) with steps (1,0), (0,1), (1,1) that don't cross the diagonal.

- S(n): 1, 2, 6, 22, 90, 394, ...
- OGF: `S(z) = (1 - z - √(1 - 6z + z²)) / (2z)`
- Functional equation: `S = 1 + z·S + z·S²` (or equivalently S satisfies a quadratic)

### Required:

1. `schroederCount : ℕ → ℕ` defined via recursion or directly
2. Sanity checks: 1, 2, 6, 22, 90 via native_decide
3. The recursion: `(n+1) * S(n+1) = 3*(2n-1)*S(n) - (n-2)*S(n-1)` for n ≥ 2
   Or simpler: verify the quadratic OGF relation.

Keep it simple — just counting formula + sanity. No CombinatorialClass needed.

## Constraints

- Must compile: `lake build AnalyticCombinatorics.PartA.Ch1.SchroederTheory`
- No sorry, no axiom
- Delete anything that doesn't compile

## Output

Write file, verify build, report.
