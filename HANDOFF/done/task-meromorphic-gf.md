# Task: Meromorphic / Rational GF Coefficients (Ch IV)

## Goal

Create `AnalyticCombinatorics/PartB/Ch4/MeromorphicCoeff.lean`.

## What to formalize

From F&S Chapter IV: Coefficients of rational generating functions via partial fractions.

1. For `1/(1-αz)^r`, the coefficient of z^n is `C(n+r-1, r-1) * α^n`.
   Define `rationalCoeff (α : ℕ) (r : ℕ) (n : ℕ) : ℕ := Nat.choose (n + r - 1) (r - 1) * α ^ n`

2. Sanity checks:
   - r=1: `rationalCoeff α 1 n = α^n` (geometric)
   - r=2: `rationalCoeff 1 2 n = n + 1`
   - r=3: `rationalCoeff 1 3 n = (n+1)*(n+2)/2` — verify for n=0..5

3. For Fibonacci: F(n) satisfies linear recurrence with char poly z²-z-1.
   - `fibRecurrence`: F(n+2) = F(n+1) + F(n) verified for n=0..10

4. Define `LinearRecurrence` structure:
   ```lean
   structure LinearRecurrence where
     order : ℕ
     coeffs : Fin order → ℤ
   ```
   
5. Verify Fibonacci satisfies its recurrence for small n.

## Imports

```lean
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic
import Mathlib.Data.Nat.Fib.Basic
```

## Constraints

- Must compile: `lake build AnalyticCombinatorics.PartB.Ch4.MeromorphicCoeff`
- No sorry, no axiom
- Delete anything that doesn't compile
- native_decide for all verifications

## Output

Write file, verify build, report.
