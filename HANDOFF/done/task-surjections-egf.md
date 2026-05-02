# Task: Surjections via EGF — Part A Ch II

## Goal

Create file `AnalyticCombinatorics/PartA/Ch2/Surjections.lean` connecting surjection counts to the EGF framework from Chapter II.

## What to formalize

The number of surjections from an n-set to a k-set is:
- `surj(n, k) = k! · S(n, k)` where S(n,k) is the Stirling number of the second kind
- Equivalently: `surj(n, k) = Σ_{j=0}^{k} (-1)^j · C(k,j) · (k-j)^n`

The EGF of surjections onto exactly k elements:
- `[z^n/n!] (e^z - 1)^k = S(n,k)` (Stirling EGF)
- `[z^n/n!] k! · (e^z - 1)^k / k! = surj(n,k) / n!`

### Required:

1. **Surjection count formula:**
   ```lean
   def surjCount (n k : ℕ) : ℤ :=
     ∑ j ∈ Finset.range (k + 1), (-1)^j * (k.choose j : ℤ) * ((k - j : ℤ) ^ n)
   ```

2. **Basic properties:**
   - `surjCount n 0 = if n = 0 then 1 else 0`
   - `surjCount 0 k = if k = 0 then 1 else 0`
   - `surjCount n n = n.factorial` for all n ≥ 1

3. **Sanity checks (inclusion-exclusion values):**
   - surjCount 1 1 = 1
   - surjCount 2 1 = 0 (can't surject 2 onto 1... wait, actually can: both map to 1... no that's not surjective onto {1}: it IS surjective. surjCount 2 1 = ... hmm.
   
   Actually surjCount(n,k) = number of surjections from n-set to k-set.
   - surjCount 2 2 = 2 (the two bijections)
   - surjCount 3 2 = 6 (3 choose to color, 2^3 - 2 = 6)
   - surjCount 3 3 = 6 (= 3!)
   - surjCount 4 2 = 14
   - surjCount 4 3 = 36

4. **Connection to the existing `Surjections.lean` example:**
   The Examples/Surjections.lean file likely has concrete counts. Add a theorem connecting:
   ```lean
   theorem surjCount_matches_example : surjCount 4 3 = 36 := by native_decide
   ```

5. **EGF connection:**
   ```lean
   theorem surjCount_egf_coeff (n k : ℕ) :
       (surjCount n k : ℚ) / n.factorial =
         coeff n (((PowerSeries.exp ℚ) - 1) ^ k)
   ```
   (This connects to the labelled framework: surjections count ordered set partitions.)

6. **Ordered Bell numbers (Fubini numbers):**
   Total surjections from n-set to any target:
   ```lean
   def fubiniNumber (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), surjCount n k
   ```
   - fubiniNumber 0 = 1
   - fubiniNumber 1 = 1
   - fubiniNumber 2 = 3
   - fubiniNumber 3 = 13
   - fubiniNumber 4 = 75

## Imports

```lean
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Combinatorics.Enumerative.Stirling
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass
import AnalyticCombinatorics.PartA.Ch2.LabelledClass
```

## Constraints

- No sorry, no axiom
- `lake build AnalyticCombinatorics.PartA.Ch2.Surjections` must pass
- If `Mathlib.Combinatorics.Enumerative.Stirling` doesn't exist or has a different path, find the correct import or define Stirling numbers locally.
- Focus on the inclusion-exclusion formula + sanity checks. The EGF connection theorem is bonus.

## Output

Write the complete file and report what you proved.
