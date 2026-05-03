# Task: Precise Catalan Asymptotics (Ch VII)

## Goal

Create `AnalyticCombinatorics/PartB/Ch7/CatalanAsymptotics.lean`.

## What to formalize

From F&S Chapter VII: The Catalan numbers have precise asymptotics `C_n ~ 4^n / (sqrt(π) * n^{3/2})`.

We can't prove this formally (requires complex analysis), but we can:

1. **Verify the asymptotic ratio converges:**
   Define `catalanRatio (n : ℕ) : ℚ := binaryTreeClass.count n * (n + 1) * 4 / (4 ^ (n + 1))`
   (This should approach 1/sqrt(π*n) ≈ 0.56/sqrt(n))
   
   Verify: `catalanRatio` is decreasing for n=1..12 (as integer cross-multiply inequalities)

2. **Motzkin growth:**
   - motzkinNumber n < 3^n for n=1..12 (native_decide)
   - motzkinNumber n > 2^n for n=4..12 (native_decide)
   - Growth rate is 3.

3. **Schroeder growth:**
   - schroederCount n < 6^n for n=1..8 (native_decide)
   - schroederCount n > 5^n for n=2..8 (native_decide... maybe 3+2√2 ≈ 5.83)
   - Actually growth is 3+2√2 ≈ 5.83. Verify: schroederCount n < 6^n and > 5^n.

4. **Transfer theorem coefficient bounds:**
   For Catalan: `binaryTreeClass.count n * (n + 1) = (2*n).choose n`
   This is the central binomial coefficient! Verify for n=0..12.

5. **Precise bound: `(2n choose n) / (n+1) ≤ 4^n / (n+1)`:**
   Verify for n=0..15 via native_decide.

## Imports

```lean
import Mathlib.Tactic
import AnalyticCombinatorics.PartA.Ch1.Trees
import AnalyticCombinatorics.PartA.Ch1.SchroederTheory
import AnalyticCombinatorics.PartB.Ch6.TransferTheorems
```

## Constraints

- Must compile: `lake build AnalyticCombinatorics.PartB.Ch7.CatalanAsymptotics`
- No sorry, no axiom
- Delete anything that doesn't compile
- native_decide for all numerical bounds
- Create directory: `AnalyticCombinatorics/PartB/Ch7/`

## Output

Write file, verify build, report.
