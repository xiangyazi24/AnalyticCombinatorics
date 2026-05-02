# Task: Algebraic Singularity Analysis (Ch VI/VII)

## Goal

Create `AnalyticCombinatorics/PartB/Ch6/AlgebraicSingularity.lean`.

## What to formalize

From F&S Chapter VI: Algebraic functions near their dominant singularity have a Puiseux expansion of the form `f(z) ~ c * (1 - z/ρ)^α` where α is typically a half-integer for square-root type singularities.

1. **Catalan asymptotics formula:**
   Define the asymptotic prediction:
   ```lean
   def catalanAsymptotic (n : ℕ) : ℚ := 4 ^ n / (n.sqrt_pi_factor)
   ```
   Actually, simpler: `C_n ~ 4^n / (sqrt(π) * n^{3/2})`.
   
   Verify the ratio `C(n) * (n+1) / 4^n` is decreasing and bounded, for n=1..15 (as Nat inequality on multiplied form).

2. **Motzkin asymptotics prediction:**
   M_n ~ c * 3^n / n^{3/2} where c = 3*sqrt(3)/(2*sqrt(π)).
   Verify `M(n) < 3^n` for n=1..15 and `M(n) > 2^n` for n=3..15.

3. **Binary tree growth bounds:**
   Already partially in Asymptotics.lean. Add:
   - `catalan_upper_4n (n : ℕ) (hn : 1 ≤ n) : binaryTreeClass.count n < 4 ^ n`
     Verify for n=1..20 via native_decide.
   - Catalan(n) > 4^n / (4*n) for n ≥ 1 (lower bound)
     Verify for n=1..15.

4. **Algebraic function definition (Prop):**
   ```lean
   def IsAlgebraicOGF (f : PowerSeries ℚ) : Prop :=
     ∃ (P : Polynomial (Polynomial ℚ)), P ≠ 0 ∧ ...
   ```
   Just define the Prop, don't prove anything about it.

## Imports

```lean
import Mathlib.Tactic
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass
import AnalyticCombinatorics.PartA.Ch1.Trees
```

## Constraints

- Must compile: `lake build AnalyticCombinatorics.PartB.Ch6.AlgebraicSingularity`
- No sorry, no axiom
- Delete anything that doesn't compile
- native_decide for all bounds
- Prop definitions are fine without proofs

## Output

Write file, verify build, report.
