# Task: Singularity Analysis Numerics (Ch VI)

## Goal

Create `AnalyticCombinatorics/PartB/Ch6/SingularityAnalysis.lean`.

## What to formalize

Numerical verification of singularity analysis predictions from Chapter VI.

1. **Transfer theorem coefficient bounds:**
   For f(z) = (1-z)^{-α}, [z^n] f ~ n^{α-1} / Γ(α).
   
   For α=1: [z^n](1-z)^{-1} = 1. Check: constant sequence.
   For α=2: [z^n](1-z)^{-2} = n+1. Check via binomial:
   ```lean
   def negBinomCoeff (alpha : ℕ) (n : ℕ) : ℕ := Nat.choose (n + alpha - 1) n
   ```
   Verify: negBinomCoeff 2 n = n + 1 for n=0..10.
   Verify: negBinomCoeff 3 n = (n+1)*(n+2)/2 for n=0..8.

2. **Logarithmic singularity coefficients:**
   [z^n] log(1/(1-z)) = 1/n for n≥1.
   ```lean
   def logCoeff (n : ℕ) : ℚ := if n = 0 then 0 else 1 / (n : ℚ)
   ```
   Verify: logCoeff 1 = 1, logCoeff 2 = 1/2, ..., logCoeff 10 = 1/10.

3. **Polylogarithm coefficients:**
   Li_s(z) = Σ_{n≥1} z^n/n^s.
   ```lean
   def polylogCoeff (s n : ℕ) : ℚ := if n = 0 then 0 else 1 / ((n : ℚ) ^ s)
   ```
   Verify: polylogCoeff 2 n = 1/n^2 for n=1..8 (these are coefficients of Li_2).

4. **Darboux's method: Catalan asymptotics check:**
   C_n ~ 4^n / (√π * n^{3/2}). Crude integer bound:
   C_n * (n+1) = C(2n,n). Verify for n=0..12.
   
   Also: C(2n,n) < 4^n for all n≥1. Verify for n=1..15.

5. **Exponential growth constant detection:**
   For Motzkin: M_n ~ c * 3^n / n^{3/2}.
   Verify: M_n < 3^n for n=1..10.
   Define Motzkin via recurrence and check.

## Imports

```lean
import Mathlib.Tactic
```

## Constraints

- Must compile: `lake build AnalyticCombinatorics.PartB.Ch6.SingularityAnalysis`
- No sorry, no axiom
- Delete anything that doesn't compile
- native_decide for all numerical checks
- **Must wrap all definitions in `namespace SingularityAnalysis`** and close with `end SingularityAnalysis`

## Output

Write file, verify build, report.
