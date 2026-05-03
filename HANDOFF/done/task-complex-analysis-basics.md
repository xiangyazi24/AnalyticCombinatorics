# Task: Complex Analysis Basics for GF (Ch IV)

## Goal

Create `AnalyticCombinatorics/PartB/Ch4/ComplexAnalysisBasics.lean`.

## What to formalize

Numerical verifications connecting complex analysis to coefficient extraction.

1. **Cauchy coefficient formula (discrete version):**
   For a polynomial P(z) = Σ a_k z^k, [z^n]P = a_n.
   Define polynomial evaluation and coefficient extraction:
   ```lean
   def polyEval (coeffs : List ℚ) (n : ℕ) : ℚ := coeffs.getD n 0
   ```
   Verify: for P = [1, 2, 3] (= 1 + 2z + 3z^2), polyEval P 0 = 1, P 1 = 2, P 2 = 3.

2. **Residue at a simple pole:**
   If f(z) = g(z)/(z-a) with g(a) ≠ 0, then Res(f, a) = g(a).
   For f(z) = 1/(1-z) = -1/(z-1): Res at z=1 is -1.
   
   For partial fractions: 1/((1-z)(1-2z)) = A/(1-z) + B/(1-2z).
   A = 1/(1-2*1) ... wait that's at pole z=1: lim_{z→1} (1-z)f(z) = 1/(1-2) = -1.
   Actually: 1/((1-z)(1-2z)) → at z=1, residue = lim_{z→1}(1-z)/((1-z)(1-2z)) = 1/(1-2) = -1.
   At z=1/2: lim_{z→1/2}(1-2z)/((1-z)(1-2z)) * (z-1/2) ... 
   
   Just verify partial fraction decomposition numerically:
   ```lean
   def partialFracCheck (n : ℕ) : Bool :=
     (2:ℤ)^(n+1) - 1 == (∑ k ∈ Finset.range (n+1), (2:ℤ)^k)
   ```

3. **Newton's identities (power sum ↔ elementary symmetric):**
   p_k = Σ x_i^k, e_k = k-th elementary symmetric polynomial.
   For x₁=1, x₂=2: e_1=3, e_2=2, p_1=3, p_2=5.
   Newton: p_1 = e_1, p_2 = p_1*e_1 - 2*e_2 = 3*3 - 2*2 = 5. ✓
   
   ```lean
   def newtonCheck2 (x1 x2 : ℤ) : Bool :=
     let e1 := x1 + x2
     let e2 := x1 * x2
     let p1 := x1 + x2
     let p2 := x1^2 + x2^2
     p1 == e1 && p2 == p1*e1 - 2*e2
   ```
   Verify for several (x1,x2) pairs.

4. **Geometric sum formula:**
   Σ_{k=0}^{n} r^k = (r^{n+1} - 1)/(r - 1) for r ≠ 1.
   In ℕ: (r-1) * Σ_{k=0}^n r^k = r^{n+1} - 1.
   ```lean
   def geomSumCheck (r n : ℕ) : Bool :=
     (r - 1) * (∑ k ∈ Finset.range (n+1), r^k) + 1 == r^(n+1)
   ```
   Verify for r=2..5, n=1..10.

5. **Roots of unity filter:**
   (1/n) * Σ_{k=0}^{n-1} ω^{jk} = [n | j] (1 if n divides j, 0 otherwise).
   For integer version: Σ_{k=0}^{n-1} ω^{jk} = n if n|j, 0 otherwise.
   
   This is hard with complex numbers. Instead verify the consequence:
   Number of binary strings of length n with weight ≡ 0 mod 3 = (2^n + 2*(-1)^n)/3 for n≥0... 
   Actually just: (2^n + 2*cos(2πn/3))/3. Skip this — too complex.
   
   Replace with: **Exponential generating function evaluation:**
   e^z at z=1 gives Σ 1/n! = e ≈ 2.718.
   Verify partial sums bound: Σ_{k=0}^10 1/k! > 2 and < 3 (as rationals).

## Imports

```lean
import Mathlib.Tactic
```

## Constraints

- Must compile: `lake build AnalyticCombinatorics.PartB.Ch4.ComplexAnalysisBasics`
- No sorry, no axiom
- Delete anything that doesn't compile
- native_decide for all checks
- **Must wrap all definitions in `namespace ComplexAnalysisBasics`** and close with `end ComplexAnalysisBasics`

## Output

Write file, verify build, report.
