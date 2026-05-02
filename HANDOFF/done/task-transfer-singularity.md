# Task: Singularity Analysis Basics — Part B Ch VI

## Goal

Extend `AnalyticCombinatorics/PartB/Ch6/TransferTheorems.lean` with concrete applications of singularity analysis.

## What to formalize

The Transfer Theorem (F&S Theorem VI.1) converts GF singularity type → coefficient asymptotics. We can't prove the full theorem (needs Hankel contours), but we can verify its predictions for known sequences.

### Required:

1. **Standard scale asymptotics — verify for geometric series:**
   - `[z^n] 1/(1-z) = 1` (simple pole at ρ=1, r=1)
   - `[z^n] 1/(1-z)^2 = n+1` (double pole, algebraic α=2)
   - `[z^n] 1/(1-z)^k = C(n+k-1, k-1)` (k-fold pole)

   ```lean
   theorem geom_coeff_pow (k n : ℕ) :
       coeff n ((1 - X)⁻¹ ^ (k+1) : PowerSeries ℚ) = (n + k).choose k
   ```

2. **Catalan asymptotics verification:**
   The Transfer Theorem predicts `C_n ~ 4^n / (n^{3/2} · √π)`.
   We can't prove this formally, but verify the exact formula:
   ```lean
   theorem catalan_formula (n : ℕ) :
       binaryTreeClass.count n = (2*n).choose n / (n + 1)
   ```
   (Needs import from Trees.lean)

3. **Darboux's formula for algebraic singularity (coefficient level):**
   For `f(z) = (1-z)^{-1/2}` (the central binomial coefficient GF):
   ```lean
   theorem centralBinom_formula (n : ℕ) :
       Nat.centralBinom n = (2*n).choose n
   ```
   (this is just a definition check against Mathlib)

4. **Exponential growth rate:**
   Define:
   ```lean
   def exponentialGrowthRate (f : ℕ → ℕ) : ℝ :=
     -- limsup (f n)^{1/n} as n → ∞
   ```
   And state (without proof) that:
   - Catalan numbers have growth rate 4
   - Motzkin numbers have growth rate 3
   - Fibonacci has growth rate φ = (1+√5)/2

   Verify numerically for small n that `(count n)^{1/n}` approaches these values.

5. **Dominant singularity principle (informal statement):**
   Just define what it means for ρ to be a dominant singularity and state the principle as a `Prop`.

## Imports

```lean
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.RingTheory.PowerSeries.Basic
import AnalyticCombinatorics.PartB.Ch6.DeltaDomain
import AnalyticCombinatorics.PartA.Ch1.Trees
```

## Constraints

- No sorry, no axiom
- `lake build AnalyticCombinatorics.PartB.Ch6.TransferTheorems` must pass
- Extend the existing file (don't overwrite the ~45 lines, add below)
- Focus on exact combinatorial identities that can be verified, not the full asymptotic machinery.

## Output

Report what you added.
