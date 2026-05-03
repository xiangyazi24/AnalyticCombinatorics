# Task: Permutation Statistics (Ch II/III)

## Goal

Create `AnalyticCombinatorics/PartA/Ch3/PermutationStatistics.lean`.

## What to formalize

Distribution of various statistics over permutations.

1. **Inversion count:**
   Total inversions over all permutations of [n] = n! * C(n,2) / 2 = n! * n*(n-1)/4.
   ```lean
   def totalInversions (n : ℕ) : ℕ := Nat.factorial n * (n * (n - 1)) / 4
   ```
   But this only works for even n*(n-1)/2... Actually n*(n-1) is always even.
   Verify: totalInversions 2 = 1, totalInversions 3 = 9, totalInversions 4 = 72

   Better: define Mahonian numbers (inversion number distribution):
   ```lean
   def inversionPoly : ℕ → ℕ → ℕ  -- [n,k] = number of perms of [n] with k inversions
   ```
   I(1,0)=1, I(2,0)=1, I(2,1)=1, I(3,0)=1, I(3,1)=2, I(3,2)=2, I(3,3)=1

2. **Major index equidistribution:**
   The major index has the same distribution as the inversion number (MacMahon).
   Define major index count and verify equality for n=3,4.

3. **Cycle type distribution:**
   Number of permutations of [n] with cycle type λ = n! / (∏ m_i! * ∏ i^{m_i}).
   
   For n=4: 
   - Type (4): 3! = 6 four-cycles
   - Type (3,1): 4!/3 = 8 
   - Type (2,2): 4!/(2!*4) = 3
   - Type (2,1,1): 4!/(2*2) = 6
   - Type (1,1,1,1): 1
   Total = 24 = 4!. Verify.

4. **Record (left-to-right maxima) count:**
   Expected number of records in a random permutation of [n] = H_n.
   Total records over all permutations = n! * H_n.
   
   Unsigned Stirling [n,k] counts perms with exactly k records (= k cycles).
   Already have unsignedStirling1 in HarmonicNumbers. Cross-verify:
   ```lean
   def totalRecords (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), k * unsignedStirling1 n k
   ```
   Hmm this uses HarmonicNumbers definitions. If importing is complex, just verify:
   Total records for n=3: perms 123(3), 132(2), 213(2), 231(2), 312(1), 321(1) → total = 11 = 3!*H_3? 6*11/6=11. Yes.

5. **Longest increasing subsequence bound:**
   For random permutations, E[LIS_n] ~ 2√n.
   Verify: for n=4, the average LIS length over all 24 perms.
   LIS lengths for S_3: 123→3, 132→2, 213→2, 231→2, 312→2, 321→1. Average = 12/6 = 2.
   Verify: 2 * 6 = 12 (total LIS sum for n=3 = 12).

## Imports

```lean
import Mathlib.Tactic
```

## Constraints

- Must compile: `lake build AnalyticCombinatorics.PartA.Ch3.PermutationStatistics`
- No sorry, no axiom
- Delete anything that doesn't compile
- native_decide for all checks
- **Must wrap all definitions in `namespace PermutationStatistics`** and close with `end PermutationStatistics`
- If the inversion polynomial recurrence is hard, use a table

## Output

Write file, verify build, report.
