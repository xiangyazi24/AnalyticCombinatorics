# Task: Derangements via EGF — Part A Ch II

## Goal

Create file `AnalyticCombinatorics/PartA/Ch2/Derangements.lean` connecting derangement counts to the EGF framework.

## What to formalize

A derangement is a permutation with no fixed points. The EGF relationship:
- `PERM = SET ⋆ DERANG` (every perm is a set of fixed points × a derangement of the rest)
- EGF: `1/(1-z) = exp(z) · D(z)` → `D(z) = exp(-z)/(1-z)`
- Coefficient: `D_n = n! · Σ_{k=0}^{n} (-1)^k / k!`

### Required:

1. **`derangeCount (n : ℕ) : ℕ`** — number of derangements of n elements:
   ```lean
   def derangeCount : ℕ → ℕ
     | 0 => 1
     | 1 => 0
     | (n + 2) => (n + 1) * (derangeCount (n + 1) + derangeCount n)
   ```

2. **Sanity checks:**
   - derangeCount 0 = 1
   - derangeCount 1 = 0
   - derangeCount 2 = 1
   - derangeCount 3 = 2
   - derangeCount 4 = 9
   - derangeCount 5 = 44

3. **Inclusion-exclusion formula:**
   ```lean
   theorem derangeCount_inclusion_exclusion (n : ℕ) :
       (derangeCount n : ℤ) = ∑ k ∈ Finset.range (n + 1), (-1)^k * (n.choose k : ℤ) * (n - k).factorial
   ```

4. **EGF coefficient:**
   ```lean
   theorem derange_egf_coeff (n : ℕ) :
       (derangeCount n : ℚ) / n.factorial = ∑ k ∈ Finset.range (n + 1), (-1 : ℚ)^k / k.factorial
   ```

5. **Relation to permutations (PERM = SET ⋆ DERANG):**
   ```lean
   theorem perm_eq_set_star_derange (n : ℕ) :
       n.factorial = ∑ k ∈ Finset.range (n + 1), n.choose k * derangeCount (n - k)
   ```

## Imports

```lean
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Int.Parity
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass
import AnalyticCombinatorics.PartA.Ch2.LabelledClass
```

## Constraints

- No sorry, no axiom
- `lake build AnalyticCombinatorics.PartA.Ch2.Derangements` must pass

## Output

Write the file and report.
