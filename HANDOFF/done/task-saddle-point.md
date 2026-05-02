# Task: Saddle-Point Method Definitions (Ch VIII)

## Goal

Create `AnalyticCombinatorics/PartB/Ch8/SaddlePoint.lean`.

## What to formalize

From F&S Chapter VIII: The saddle-point method applies to entire functions (infinite radius of convergence) like `e^z`.

1. **Exponential generating function coefficients:**
   - `expCoeff (n : ℕ) : ℚ := 1 / n.factorial` (coefficient of z^n in e^z)
   - Verify: n.factorial * expCoeff n = 1 for n=0..10

2. **Bell number EGF verification:**
   - EGF of Bell numbers is `exp(e^z - 1)`.
   - Verify: `bellCount n * n.factorial` gives the right prefactored count.
   - Actually: `bellCount n = [z^n] exp(e^z - 1) * n!`
   - Cross-verify with BellNumbers.lean values for n=0..8 (native_decide).

3. **Integer partition generating function (Euler):**
   - Product formula: `∏_{k≥1} 1/(1-z^k)`
   - Verify first few coefficients: p(0)=1, p(1)=1, p(2)=2, p(3)=3, p(4)=5, p(5)=7
   - Cross-check with IntPartTheory values.

4. **Saddle-point definitions (Prop-valued):**
   ```lean
   def IsSaddlePointApplicable (f : ℕ → ℕ) : Prop :=
     ∀ n, ∃ C > 0, f n ≤ C * (f n)  -- placeholder
   ```
   
   Better: define `hasSuperExponentialGrowth`:
   ```lean
   def hasSuperExponentialGrowth (f : ℕ → ℕ) : Prop :=
     ∀ ρ : ℕ, ∃ N, ∀ n > N, f n > ρ ^ n
   ```
   - Verify `n.factorial` has super-exponential growth for ρ = 1..5, n up to some bound.

## Imports

```lean
import Mathlib.Tactic
import AnalyticCombinatorics.PartA.Ch2.BellNumbers
```

## Constraints

- Must compile: `lake build AnalyticCombinatorics.PartB.Ch8.SaddlePoint`
- No sorry, no axiom
- Delete anything that doesn't compile
- native_decide for verifications
- Prop definitions for framework (no hard proofs)
- Create directory if needed: `AnalyticCombinatorics/PartB/Ch8/`

## Output

Write file, verify build, report.
