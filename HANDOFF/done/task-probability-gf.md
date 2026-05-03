# Task: Probability Generating Functions (Ch III/IX)

## Goal

Create `AnalyticCombinatorics/PartA/Ch3/ProbabilityGF.lean`.

## What to formalize

Probability generating functions and their moment computations.

1. **Binomial distribution PGF:**
   PGF of Binomial(n,p): (1-p+pu)^n.
   Mean = np, variance = np(1-p).
   
   Verify via coefficient extraction for small cases:
   ```lean
   def binomialPGFCoeff (n k : ℕ) : ℚ := (Nat.choose n k : ℚ) / (2:ℚ)^n
   ```
   For p=1/2: coefficients of (1/2 + u/2)^n are C(n,k)/2^n.
   Verify: Σ_k k * C(n,k) / 2^n = n/2 (mean) for n=4,6,8.

2. **Poisson distribution PGF:**
   PGF: e^{λ(u-1)}.
   Mean = λ, Variance = λ.
   
   Truncated version for λ=1:
   ```lean
   def poissonCoeff (k : ℕ) : ℚ := 1 / (Nat.factorial k : ℚ)
   ```
   Verify: Σ_{k=0}^{10} poissonCoeff k approaches 1 (from below):
   Σ_{k=0}^{10} 1/k! = 9864101/3628800 (verify this fraction).

3. **Geometric distribution PGF:**
   PGF of Geometric(p): p/(1-(1-p)u) for u < 1/(1-p).
   Mean = 1/p, variance = (1-p)/p^2.
   
   For p=1/2: P(X=k) = (1/2)^k for k≥1. PGF = u/2 / (1 - u/2) = u/(2-u).
   Actually Geometric starting from 1: P(X=k) = p(1-p)^{k-1}.
   
   ```lean
   def geomProbNumer (k : ℕ) : ℕ := 1  -- For p=1/2: numerator is 1
   def geomProbDenom (k : ℕ) : ℕ := 2^k  -- denominator is 2^k
   ```
   Verify: Σ_{k=1}^n 1/2^k = 1 - 1/2^n. Check for n=1..8.

4. **Factorial moments from PGF:**
   E[X(X-1)...(X-k+1)] = PGF^{(k)}(1).
   For Poisson(λ): k-th factorial moment = λ^k.
   
   ```lean
   def fallingFactorial (n k : ℕ) : ℕ := ∏ i ∈ Finset.range k, (n - i)
   ```
   Verify: fallingFactorial 5 2 = 20, fallingFactorial 5 3 = 60.

5. **Variance from factorial moments:**
   Var(X) = E[X(X-1)] + E[X] - (E[X])^2.
   For Binomial(n, 1/2): E[X] = n/2, E[X(X-1)] = n(n-1)/4.
   Var = n(n-1)/4 + n/2 - n^2/4 = n/4.
   
   Verify in ℚ for n=4,6,8:
   ```lean
   def binomialVarianceCheck (n : ℕ) : Bool :=
     (n : ℚ) * (n - 1) / 4 + (n : ℚ) / 2 - ((n : ℚ) / 2)^2 == (n : ℚ) / 4
   ```

## Imports

```lean
import Mathlib.Tactic
```

## Constraints

- Must compile: `lake build AnalyticCombinatorics.PartA.Ch3.ProbabilityGF`
- No sorry, no axiom
- Delete anything that doesn't compile
- native_decide for all checks
- **Must wrap all definitions in `namespace ProbabilityGF`** and close with `end ProbabilityGF`

## Output

Write file, verify build, report.
