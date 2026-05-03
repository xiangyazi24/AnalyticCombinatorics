# Task: Urns and Occupancy (Ch II/IX)

## Goal

Create `AnalyticCombinatorics/PartA/Ch2/UrnsOccupancy.lean`.

## What to formalize

Urn models and occupancy problems from analytic combinatorics.

1. **Occupancy numbers:**
   n balls into m urns: total arrangements = m^n.
   With ≥1 ball per urn (surjections): m! * S(n,m) where S is Stirling 2nd kind.
   ```lean
   def occupancyTotal (m n : ℕ) : ℕ := m ^ n
   
   def stirling2 : ℕ → ℕ → ℕ
     | 0, 0 => 1
     | 0, _ + 1 => 0
     | _ + 1, 0 => 0
     | n + 1, k + 1 => (k + 1) * stirling2 n (k + 1) + stirling2 n k
   
   def surjectionCount (n m : ℕ) : ℕ := Nat.factorial m * stirling2 n m
   ```
   Verify: surjectionCount 4 2 = 14, surjectionCount 4 3 = 36, surjectionCount 5 3 = 150

2. **Expected number of empty urns:**
   E[empty] = m * (1 - 1/m)^n = m * ((m-1)/m)^n.
   ```lean
   def expectedEmptyNumer (m n : ℕ) : ℕ := m * (m - 1)^n
   def expectedEmptyDenom (m n : ℕ) : ℕ := m^n
   ```
   Verify: expectedEmptyNumer 4 3 / expectedEmptyDenom 4 3 ... 
   Actually: for m=4, n=3: E[empty] = 4*(3/4)^3 = 4*27/64 = 27/16 ≈ 1.69.
   Verify: expectedEmptyNumer 4 3 = 108, expectedEmptyDenom 4 3 = 64.

3. **Coupon collector:**
   Expected time to collect all m coupons = m * H_m.
   ```lean
   def couponCollectorExpected (m : ℕ) : ℚ := (m : ℚ) * ∑ k ∈ Finset.range m, 1 / ((k + 1) : ℚ)
   ```
   Verify: couponCollectorExpected 1 = 1, couponCollectorExpected 2 = 3,
   couponCollectorExpected 3 = 11/2, couponCollectorExpected 4 = 25/3

4. **Multinomial coefficient:**
   ```lean
   def multinomialCoeff (ns : List ℕ) : ℕ :=
     Nat.factorial (ns.sum) / (ns.map Nat.factorial).prod
   ```
   Verify: multinomialCoeff [2,2,2] = 90, multinomialCoeff [3,2,1] = 60,
   multinomialCoeff [4,4] = 70

5. **Balls in bins — maximum load:**
   With n balls in n bins, max load ≈ ln n / ln ln n.
   Just verify: for n=4, possible max loads. Number of arrangements with max load ≤ 1 = 4! = 24.
   Fraction with max ≤ 1: 24/256. Verify: 4^4 = 256 and 4! = 24.
   ```lean
   example : (4:ℕ)^4 = 256 := by native_decide
   example : Nat.factorial 4 = 24 := by native_decide
   example : 24 * 11 < 256 := by native_decide  -- less than 1/11 chance of all distinct
   ```
   Wait 24/256 < 1/10: 24*10 = 240 < 256. 

## Imports

```lean
import Mathlib.Tactic
```

## Constraints

- Must compile: `lake build AnalyticCombinatorics.PartA.Ch2.UrnsOccupancy`
- No sorry, no axiom
- Delete anything that doesn't compile
- native_decide for all checks
- **Must wrap all definitions in `namespace UrnsOccupancy`** and close with `end UrnsOccupancy`

## Output

Write file, verify build, report.
