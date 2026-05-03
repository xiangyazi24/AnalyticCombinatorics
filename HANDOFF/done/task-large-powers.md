# Task: Large Powers and Central Limit (Ch IX)

## Goal

Create `AnalyticCombinatorics/PartB/Ch9/LargePowers.lean`.

## What to formalize

Central limit theorem applications and large deviation bounds.

1. **Gaussian approximation quality:**
   For Binomial(n, 1/2): P(X = n/2) ≈ √(2/(πn)).
   Exact: C(n, n/2) / 2^n.
   
   Verify: C(100, 50) / 2^100 bounds... too large. Use smaller:
   ```lean
   -- C(10,5) = 252, 2^10 = 1024. Ratio = 252/1024 ≈ 0.246.
   -- √(2/(π*10)) ≈ √(0.0637) ≈ 0.252. Close!
   example : Nat.choose 10 5 = 252 := by native_decide
   example : 252 * 4 < 1024 := by native_decide  -- ratio < 1/4
   example : 252 * 5 > 1024 := by native_decide  -- ratio > 1/5
   ```

2. **Chernoff bound verification:**
   For X ~ Binomial(n, 1/2): P(X ≥ (1+δ)n/2) ≤ exp(-nδ²/6).
   
   Exact tail: Σ_{k=⌈(1+δ)n/2⌉}^n C(n,k)/2^n.
   For n=10, δ=0.5: threshold = 7.5, so P(X≥8).
   P(X≥8) = (C(10,8)+C(10,9)+C(10,10))/2^10 = (45+10+1)/1024 = 56/1024.
   Chernoff: exp(-10*0.25/6) ≈ exp(-0.417) ≈ 0.659. Very loose for small n.
   
   Just verify the exact tail:
   ```lean
   def binomialTailNumer (n threshold : ℕ) : ℕ :=
     ∑ k ∈ Finset.range (n - threshold + 1), Nat.choose n (threshold + k)
   ```
   Verify: binomialTailNumer 10 8 = 56 (= C(10,8)+C(10,9)+C(10,10) = 45+10+1).

3. **Law of large numbers illustration:**
   Σ_{k=⌊n/3⌋}^{⌈2n/3⌉} C(n,k)/2^n → 1 as n→∞.
   
   For n=12: sum from k=4 to k=8 of C(12,k) vs 2^12 = 4096.
   ```lean
   def centralMass (n lo hi : ℕ) : ℕ :=
     ∑ k ∈ Finset.range (hi - lo + 1), Nat.choose n (lo + k)
   ```
   Verify: centralMass 12 4 8 > 3*4096/4 (more than 75% is in middle third).

4. **Entropy function:**
   Binary entropy H(p) = -p*log(p) - (1-p)*log(1-p).
   At p=1/2: H(1/2) = log(2) = 1 bit.
   
   Connection: C(n, pn) ≈ 2^{nH(p)}.
   For p=1/4, n=8: C(8,2) = 28. H(1/4) = -(1/4)log(1/4)-(3/4)log(3/4) ≈ 0.811.
   2^{8*0.811} ≈ 2^{6.49} ≈ 90. And C(8,2) = 28. (Crude approximation.)
   
   Just verify: C(n, n/2) ≤ 2^n for all n (trivial from sum), and C(n,1) = n < 2^n for n≥1.
   ```lean
   example : Nat.choose 20 10 < 2^20 := by native_decide
   example : Nat.choose 20 5 < 2^20 := by native_decide
   ```

5. **Large deviation: binomial concentration:**
   C(n, k) ≤ 2^n for all k. (Obvious: sum of all C(n,k) = 2^n.)
   C(n, k) ≤ C(n, n/2) (maximized at center).
   ```lean
   example : Nat.choose 10 3 ≤ Nat.choose 10 5 := by native_decide
   example : Nat.choose 10 7 ≤ Nat.choose 10 5 := by native_decide
   example : Nat.choose 12 4 ≤ Nat.choose 12 6 := by native_decide
   example : Nat.choose 20 7 ≤ Nat.choose 20 10 := by native_decide
   ```

## Imports

```lean
import Mathlib.Tactic
```

## Constraints

- Must compile: `lake build AnalyticCombinatorics.PartB.Ch9.LargePowers`
- No sorry, no axiom
- Delete anything that doesn't compile
- native_decide for all checks
- **Must wrap all definitions in `namespace LargePowers`** and close with `end LargePowers`

## Output

Write file, verify build, report.
