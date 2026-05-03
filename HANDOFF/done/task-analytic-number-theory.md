# Task: Analytic Number Theory Connections (Ch II/IX appendix)

## Goal

Create `AnalyticCombinatorics/PartA/Ch2/AnalyticNumberTheory.lean`.

## What to formalize

Connections between analytic combinatorics and number theory from F&S appendices.

1. **Divisor function σ_k(n):**
   ```lean
   def divisorSigma (k n : ℕ) : ℕ := ∑ d ∈ Nat.divisors n, d ^ k
   ```
   
   Verify:
   - σ_0(12) = 6 (number of divisors)
   - σ_1(12) = 28 (sum of divisors)
   - σ_0(1) = 1, σ_0(p) = 2 for prime p

2. **Euler's totient at specific values:**
   Verify φ(n) for n=1..12 matches Nat.totient from Mathlib.
   
   φ(1)=1, φ(2)=1, φ(3)=2, φ(4)=2, φ(5)=4, φ(6)=2,
   φ(7)=6, φ(8)=4, φ(9)=6, φ(10)=4, φ(11)=10, φ(12)=4

3. **Möbius function (using ℤ):**
   ```lean
   def mobiusFunction : ℕ → ℤ
     | 0 => 0
     | 1 => 1
     | n + 2 => -(∑ d ∈ (Nat.divisors (n + 2)).filter (· < n + 2), mobiusFunction d)
   ```
   
   Verify: μ(1)=1, μ(2)=-1, μ(3)=-1, μ(4)=0, μ(5)=-1, μ(6)=1

4. **Möbius inversion verification:**
   If f(n) = Σ_{d|n} g(d), then g(n) = Σ_{d|n} μ(n/d) * f(d).
   
   Take f = σ_0 (number of divisors), g = 1 (constant 1).
   Verify: Σ_{d|n} μ(n/d) * σ_0(d) = 1 for n=1..10.
   
   Actually that's not quite right. Take f(n) = n, g(n) = φ(n).
   Verify: Σ_{d|n} φ(d) = n for n=1..12.

5. **Number of squarefree integers up to n:**
   Q(n) = |{k ≤ n : k is squarefree}|
   Asymptotically Q(n) ~ 6n/π², but just verify small values:
   ```lean
   def squarefreeCount (n : ℕ) : ℕ := (Finset.range n).filter isSquarefree |>.card
   ```
   Q(10) = 7, Q(20) = 12, Q(30) = 19

## Imports

```lean
import Mathlib.Tactic
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Totient
```

## Constraints

- Must compile: `lake build AnalyticCombinatorics.PartA.Ch2.AnalyticNumberTheory`
- No sorry, no axiom
- Delete anything that doesn't compile
- native_decide for all checks
- Termination for mobiusFunction might be tricky — use well_founded_tactics or a direct table if needed
- **Must wrap all definitions in `namespace AnalyticNumberTheory`** and close with `end AnalyticNumberTheory`

## Output

Write file, verify build, report.
