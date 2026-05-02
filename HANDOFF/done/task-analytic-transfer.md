# Task: Analytic Transfer Lemmas (Part B Ch6 extension)

## Goal

Create `AnalyticCombinatorics/PartB/Ch6/Transfer.lean` with concrete transfer theorem applications.

## What to formalize

From F&S Chapter VI: The transfer theorems relate singularity type to coefficient asymptotics.

### Required:

1. **Singularity types as definitions:**
   ```lean
   structure SingularExpansion where
     rho : ℚ  -- location of dominant singularity (radius of convergence)
     alpha : ℚ  -- exponent in (1 - z/ρ)^α
     const : ℚ  -- leading constant
   ```

2. **Coefficient predictions:** Given a singular expansion, the predicted coefficient is:
   `[z^n] ~ const * rho^{-n} * n^{-alpha-1} / Gamma(-alpha)`
   
   For alpha = -1/2 (square root): [z^n] ~ const * rho^{-n} / (sqrt(pi*n))
   For alpha = -3/2: [z^n] ~ const * rho^{-n} * sqrt(n/pi)

3. **Catalan transfer verification:**
   - Catalan OGF has singularity at z=1/4 with exponent -1/2
   - Prediction: C_n ~ 4^n / (sqrt(pi*n))
   - Verify ratio C_n * sqrt(n) * pi / 4^n → 1 for n=10..20 (within 10% say)
   - Actually just verify the integer inequality version:
     `C_n * (n+1) ≤ 4^n` and `4^n ≤ C_n * (4*n + 2)` for small n

4. **Motzkin transfer:**
   - Singularity at z=1/3, exponent -1/2
   - M_n ~ c * 3^n / sqrt(n) for some constant c
   - Verify M_n * n < K * 3^n for suitable K, n=5..15

Keep everything in ℕ or ℚ to avoid Real difficulties. Use integer cross-multiplication for ratio checks.

## Imports

```lean
import Mathlib.Tactic
import AnalyticCombinatorics.PartA.Ch1.Trees
```

## Constraints

- Must compile: `lake build AnalyticCombinatorics.PartB.Ch6.Transfer`
- No sorry, no axiom
- Delete anything that doesn't compile
- Prefer native_decide for all verifications

## Output

Write file, verify build, report.
