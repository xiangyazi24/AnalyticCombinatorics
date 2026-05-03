# Task: Analytic Depoissonization (Ch IX)

## Goal

Create `AnalyticCombinatorics/PartB/Ch9/Depoissonization.lean`.

## What to formalize

Numerical verifications related to Poisson models and depoissonization from Ch IX.

1. **Poisson probabilities (truncated):**
   P(X=k) = λ^k * e^{-λ} / k! for Poisson(λ).
   
   Work with rational approximation: for λ=1, the probabilities times e are:
   ```lean
   def poissonNumerator (k : ℕ) : ℕ := 1  -- λ^k / k! * e * k! = 1 for λ=1
   -- Actually: P(X=k) * k! * e = λ^k for λ=1, so just 1.
   -- Better: verify that Σ_{k=0}^n 1/k! approaches e.
   ```
   
   Partial sums of 1/k!:
   ```lean
   def expPartialSum (n : ℕ) : ℚ := ∑ k ∈ Finset.range (n + 1), 1 / (Nat.factorial k : ℚ)
   ```
   Verify: expPartialSum 0 = 1, expPartialSum 1 = 2, expPartialSum 2 = 5/2,
   expPartialSum 3 = 8/3, expPartialSum 4 = 65/24, expPartialSum 5 = 163/60

2. **Poisson mean and variance verification:**
   For Poisson(λ): E[X] = λ, Var(X) = λ.
   
   Verify with truncated sums (λ=3, truncate at 15):
   ```lean
   def poissonMeanApprox (lam : ℕ) (trunc : ℕ) : ℚ :=
     (∑ k ∈ Finset.range trunc, (k : ℚ) * (lam : ℚ)^k / (Nat.factorial k : ℚ)) /
     (∑ k ∈ Finset.range trunc, (lam : ℚ)^k / (Nat.factorial k : ℚ))
   ```
   This might be too complex. Simpler:

3. **Birthday problem connection:**
   Probability of no collision among k items in n bins ≈ e^{-k²/(2n)}.
   
   Exact: ∏_{i=0}^{k-1} (n-i)/n = n!/(n^k * (n-k)!).
   ```lean
   def birthdayNoColl (n k : ℕ) : ℚ :=
     if k > n then 0
     else (Nat.factorial n : ℚ) / ((n : ℚ)^k * (Nat.factorial (n-k) : ℚ))
   ```
   Verify: birthdayNoColl 365 23 < 1/2 (as rationals — this might overflow).
   
   Actually just verify small cases:
   birthdayNoColl 4 2 = 3/4, birthdayNoColl 4 3 = 3/8

4. **Stirling numbers of the 2nd kind (set partitions → hashing):**
   ```lean
   def stirling2 : ℕ → ℕ → ℕ
     | 0, 0 => 1
     | 0, _ + 1 => 0
     | _ + 1, 0 => 0
     | n + 1, k + 1 => (k + 1) * stirling2 n (k + 1) + stirling2 n k
   ```
   Verify: stirling2 4 2 = 7, stirling2 5 2 = 15, stirling2 5 3 = 25

5. **Hashing: expected collisions:**
   In a hash table of size m with n keys:
   Expected empty slots = m * (1 - 1/m)^n.
   
   For m=10, n=5: expected empty = 10 * (9/10)^5 = 10 * 59049/100000.
   ```lean
   def expectedEmpty (m n : ℕ) : ℚ := (m : ℚ) * ((m - 1 : ℚ) / (m : ℚ))^n
   ```
   Verify: expectedEmpty 10 5 = 59049/10000 (approximately 5.9)

## Imports

```lean
import Mathlib.Tactic
```

## Constraints

- Must compile: `lake build AnalyticCombinatorics.PartB.Ch9.Depoissonization`
- No sorry, no axiom
- Delete anything that doesn't compile
- native_decide for all checks
- **Must wrap all definitions in `namespace Depoissonization`** and close with `end Depoissonization`

## Output

Write file, verify build, report.
