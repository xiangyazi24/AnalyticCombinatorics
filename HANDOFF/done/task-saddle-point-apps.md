# Task: Saddle-Point Applications (Ch VIII)

## Goal

Create `AnalyticCombinatorics/PartB/Ch8/SaddlePointApps.lean`.

## What to formalize

Numerical verifications related to saddle-point method applications from Chapter VIII.

1. **Set partitions (Bell numbers via Dobinski):**
   B_n = (1/e) * Σ_{k≥0} k^n / k!
   
   Truncated Dobinski sum:
   ```lean
   def dobinskiTrunc (n trunc : ℕ) : ℚ :=
     ∑ k ∈ Finset.range trunc, (k : ℚ)^n / (Nat.factorial k : ℚ)
   ```
   
   Bell numbers: B_0=1, B_1=1, B_2=2, B_3=5, B_4=15, B_5=52, B_6=203, B_7=877
   
   The Dobinski sum (without 1/e factor) should approximate B_n * e.
   Verify: dobinskiTrunc n 20 is close to B_n * (Σ_{k=0}^{19} 1/k!):
   Actually just verify Bell numbers directly via the triangle:
   ```lean
   def bellTriangle : ℕ → ℕ → ℕ
     | 0, 0 => 1
     | 0, _ + 1 => 0
     | n + 1, 0 => bellTriangle n n
     | n + 1, k + 1 => bellTriangle (n + 1) k + bellTriangle n k
   
   def bellNumber (n : ℕ) : ℕ := bellTriangle n 0
   ```
   Verify bellNumber n for n=0..7 matches expected values.

2. **Integer partitions with distinct parts vs odd parts:**
   |{partitions of n into distinct parts}| = |{partitions of n into odd parts}| (Euler).
   
   Define both and verify equality for n=1..12:
   ```lean
   def distinctPartitions (n : ℕ) : ℕ := -- count partitions into distinct parts
   def oddPartitions (n : ℕ) : ℕ := -- count partitions into odd parts
   ```
   Values: 1,1,1,2,2,3,4,5,6,8,10,12 for n=0..11.

3. **Surjection numbers via inclusion-exclusion:**
   S(n,k) = Σ_{j=0}^k (-1)^j * C(k,j) * (k-j)^n = k! * Stirling2(n,k).
   
   Verify: surjectionCount 4 2 = 14, surjectionCount 4 3 = 36, surjectionCount 5 3 = 150.
   ```lean
   def surjectionCount (n k : ℕ) : ℕ :=
     -- inclusion-exclusion
     sorry -- use existing definition or recompute
   ```
   
   Actually just verify Stirling2 * k! = surjection formula for small values.

4. **Central Stirling numbers:**
   ```lean
   def centralStirling2 (n : ℕ) : ℕ := stirling2 (2*n) n
   ```
   where stirling2 is Stirling numbers of 2nd kind.
   Hmm, this might be too expensive. Just verify small cases.

5. **Saddle-point approximation quality for Bell:**
   The saddle-point gives B_n ~ n^n * ... 
   Just verify that B_n < n^n for n≥2 and B_n > 2^(n-1) for n≥1:
   ```lean
   example : bellNumber 5 < 5^5 := by native_decide
   example : bellNumber 6 < 6^6 := by native_decide
   example : bellNumber 5 > 2^4 := by native_decide
   example : bellNumber 7 > 2^6 := by native_decide
   ```

## Imports

```lean
import Mathlib.Tactic
```

## Constraints

- Must compile: `lake build AnalyticCombinatorics.PartB.Ch8.SaddlePointApps`
- No sorry, no axiom
- Delete anything that doesn't compile
- native_decide for all checks
- **Must wrap all definitions in `namespace SaddlePointApps`** and close with `end SaddlePointApps`
- Bell triangle termination should be straightforward (lexicographic on (n,k))

## Output

Write file, verify build, report.
