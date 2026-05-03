# Task: Formal Power Series Coefficient Extraction (Ch IV)

## Goal

Create `AnalyticCombinatorics/PartB/Ch4/FormalPowerSeries.lean`.

## What to formalize

Work with Mathlib's PowerSeries to extract and verify coefficients.

1. **Exponential series coefficients:**
   [z^n] exp(z) = 1/n! in ℚ[[z]].
   
   ```lean
   example : PowerSeries.coeff 0 (PowerSeries.exp ℚ) = 1 := by simp
   example : PowerSeries.coeff 1 (PowerSeries.exp ℚ) = 1 := by simp
   example : PowerSeries.coeff 2 (PowerSeries.exp ℚ) = 1/2 := by simp; ring
   ```

2. **Geometric series inverse:**
   (1 - X)⁻¹ has all coefficients = 1.
   Already in TransferTheorems. Cross-verify:
   ```lean
   example : PowerSeries.coeff 5 ((1 - PowerSeries.X : PowerSeries ℚ)⁻¹) = 1 := by ...
   ```

3. **Product of power series:**
   (1 + X + X^2) * (1 + X) = 1 + 2X + 2X^2 + X^3.
   Verify coefficients.

4. **Composition (substitution):**
   If F(z) = Σ f_n z^n and G(z) = Σ g_n z^n with g_0 = 0,
   then F(G(z)) is well-defined.
   
   For F = 1/(1-z), G = z^2: F(G(z)) = 1/(1-z^2) = 1 + z^2 + z^4 + ...
   Verify: [z^0] = 1, [z^1] = 0, [z^2] = 1, [z^3] = 0, [z^4] = 1.

5. **Derivative of power series:**
   If F(z) = Σ f_n z^n, then F'(z) = Σ (n+1) f_{n+1} z^n.
   
   Verify: derivative of exp(z) = exp(z), i.e., coefficients match.

## Imports

```lean
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Tactic
```

## Constraints

- Must compile: `lake build AnalyticCombinatorics.PartB.Ch4.FormalPowerSeries`
- No sorry, no axiom
- Delete anything that doesn't compile
- Use ℚ as the coefficient ring (exact arithmetic)
- If proofs about PowerSeries are too hard, fall back to coefficient-level verification
- **Must wrap all definitions in `namespace FormalPowerSeries`** and close with `end FormalPowerSeries`

## Output

Write file, verify build, report.
