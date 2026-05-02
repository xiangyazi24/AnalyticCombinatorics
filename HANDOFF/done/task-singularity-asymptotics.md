# Task: Singularity Analysis Asymptotics (Ch VI)

## Goal

Create `AnalyticCombinatorics/PartB/Ch6/Asymptotics.lean`.

## What to formalize

From F&S Chapter VI: Standard function scale and asymptotic transfer.

1. Define the standard function scale coefficients:
   ```lean
   def standardScaleCoeff (α : ℚ) (n : ℕ) : ℚ := ...
   ```
   For `(1-z)^{-α}`, coeff of z^n is `C(n+α-1, n)` generalized.
   
   Simplify: just verify for integer α cases.

2. `geomCoeff (ρ : ℕ) (n : ℕ) : ℕ := ρ ^ n`
   Verify: coefficient of z^n in 1/(1-ρz) is ρ^n.

3. **Catalan asymptotics predicate** (statement only):
   `catalanAsymptotics : Prop := ∀ ε > 0, ∃ N, ∀ n > N, ...`
   
   Or simpler: verify the ratio `C(n+1)/C(n)` approaches 4 for small n:
   - C(n+1)/C(n) for n=5..10, verify each is between 3 and 5 (as ℕ inequalities on multiplied form)

4. **Exponential growth verification** for sequences:
   - Catalan: `4^n > binaryTreeClass.count n` for n = 1..15 (native_decide)
   - Catalan: `3^n < binaryTreeClass.count n` for n = 5..15 (native_decide)
   
5. Define `IsExponentialOrder (f : ℕ → ℕ) (ρ : ℕ) : Prop` meaning growth rate is ρ.

## Imports

```lean
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass
import AnalyticCombinatorics.PartA.Ch1.Trees
```

## Constraints

- Must compile: `lake build AnalyticCombinatorics.PartB.Ch6.Asymptotics`
- No sorry, no axiom
- Delete anything that doesn't compile
- Use native_decide for inequalities
- Prop-valued asymptotic statements are fine (just definitions, no proofs needed)

## Output

Write file, verify build, report.
