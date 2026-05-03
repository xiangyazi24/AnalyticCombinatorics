# Task: Special Numbers in Combinatorics (Ch II/III)

## Goal

Create `AnalyticCombinatorics/PartA/Ch2/SpecialNumbers.lean`.

## What to formalize

Key number-theoretic sequences that arise in analytic combinatorics.

1. **Bernoulli numbers (rational):**
   ```lean
   def bernoulliNumber : ℕ → ℚ
     | 0 => 1
     | n + 1 => -(∑ k ∈ Finset.range (n + 1),
                    (Nat.choose (n + 2) k : ℚ) * bernoulliNumber k) / (n + 2 : ℚ)
   ```
   Verify: B_0 = 1, B_1 = -1/2, B_2 = 1/6, B_3 = 0, B_4 = -1/30, B_6 = 1/42

2. **Fibonacci-related identities:**
   ```lean
   -- Already have Nat.fib, verify identities
   ```
   - Cassini's identity: fib(n-1)*fib(n+1) - fib(n)^2 = (-1)^n
     Verify as: fib(n+1)*fib(n-1) + (if n % 2 = 0 then 1 else 0) = fib(n)^2 + (if n % 2 = 1 then 1 else 0)
     Or better: |fib(n-1)*fib(n+1) - fib(n)^2| = 1 for n≥1.
     In ℤ: (Nat.fib (n+2) : ℤ) * Nat.fib n - (Nat.fib (n+1) : ℤ)^2 = (-1)^(n+1) for n=0..15.
   
   - Sum of first n Fibonacci: fib(1)+...+fib(n) = fib(n+2) - 1. Verify for n=1..12.

3. **Catalan number identities:**
   ```lean
   def catalanNum (n : ℕ) : ℕ := Nat.choose (2*n) n / (n + 1)
   ```
   - Segner recurrence: C_n = Σ_{k=0}^{n-1} C_k * C_{n-1-k}. Verify for n=1..8.
   - C_n = C(2n,n) - C(2n,n+1). Verify for n=0..10.

4. **Ballot numbers:**
   ```lean
   def ballotNumber (n k : ℕ) : ℕ := 
     if k > n then 0
     else if n = 0 && k = 0 then 1
     else (k + 1) * Nat.choose (n + k) n / (n + 1)  -- not quite
   ```
   Actually use the Bertrand ballot problem: # favorable sequences where A stays ahead = (a-b)/(a+b) * C(a+b, a).
   
   Simpler: Narayana numbers N(n,k) = (1/n) * C(n,k) * C(n,k-1) for 1≤k≤n.
   ```lean
   def narayana (n k : ℕ) : ℕ :=
     if n = 0 || k = 0 || k > n then 0
     else Nat.choose n k * Nat.choose n (k-1) / n
   ```
   Verify: narayana 4 1 = 1, narayana 4 2 = 6, narayana 4 3 = 6, narayana 4 4 = 1
   Row sum: Σ_k narayana(n,k) = C_n. Verify for n=1..6.

5. **Lah numbers:**
   L(n,k) = C(n-1, k-1) * n! / k!
   ```lean
   def lahNumber (n k : ℕ) : ℕ :=
     if k = 0 then (if n = 0 then 1 else 0)
     else Nat.choose (n - 1) (k - 1) * Nat.factorial n / Nat.factorial k
   ```
   Verify: L(3,1)=6, L(3,2)=6, L(3,3)=1, L(4,1)=24, L(4,2)=36, L(4,3)=12, L(4,4)=1

## Imports

```lean
import Mathlib.Tactic
```

## Constraints

- Must compile: `lake build AnalyticCombinatorics.PartA.Ch2.SpecialNumbers`
- No sorry, no axiom
- Delete anything that doesn't compile
- native_decide for all checks
- **Must wrap all definitions in `namespace SpecialNumbers`** and close with `end SpecialNumbers`

## Output

Write file, verify build, report.
