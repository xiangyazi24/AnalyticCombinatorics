# Task: Harmonic Numbers and Cycle Statistics (Ch II/IX)

## Goal

Create `AnalyticCombinatorics/PartA/Ch2/HarmonicNumbers.lean`.

## What to formalize

Harmonic numbers H_n = 1 + 1/2 + ... + 1/n appear in the expected number of
cycles in a random permutation: E[cycles in σ ∈ S_n] = H_n.

1. **Rational harmonic number:**
   ```lean
   def harmonicNumber : ℕ → ℚ
     | 0 => 0
     | n + 1 => harmonicNumber n + 1 / (n + 1 : ℚ)
   ```

2. **Sanity checks (native_decide on ℚ):**
   - H(1) = 1
   - H(2) = 3/2
   - H(3) = 11/6
   - H(4) = 25/12
   - H(5) = 137/60
   - H(6) = 49/20

3. **Total number of cycles across all permutations of [n]:**
   `totalCycles (n : ℕ) : ℕ` — sum of number of cycles over all σ ∈ S_n
   
   Formula: totalCycles n = |s(n,1)| + |s(n,2)| + ... + |s(n,n)|
   where s(n,k) = unsigned Stirling numbers of first kind.
   
   Actually: totalCycles n = Σ_{k=1}^{n} |s(n,k)| * k... no.
   
   Simpler: totalCycles n = n! * H_n (this is the expected value * n!).
   
   But n! * H_n might not be integer... actually it is:
   n! * H_n = n! * (1 + 1/2 + ... + 1/n) = Σ_{k=1}^{n} n!/k
   
   Each n!/k is an integer for k ≤ n. So yes, always integer.
   
   Define: `totalCyclesCount (n : ℕ) : ℕ := ∑ k ∈ Finset.range n, n.factorial / (k + 1)`

4. **Verify totalCyclesCount = n! * H_n (as rationals) for n=1..6:**
   ```lean
   example : (totalCyclesCount 4 : ℚ) = 4! * harmonicNumber 4 := by native_decide
   ```

5. **Unsigned Stirling numbers of the first kind (signless):**
   `unsignedStirling1 (n k : ℕ) : ℕ` — number of permutations of [n] with exactly k cycles.
   
   Recursion: c(n+1, k) = n * c(n, k) + c(n, k-1)
   Base: c(0, 0) = 1, c(n, 0) = 0 for n ≥ 1, c(0, k) = 0 for k ≥ 1
   
   Verify: c(3,1) = 2, c(3,2) = 3, c(3,3) = 1 (sum = 6 = 3!)
   c(4,1) = 6, c(4,2) = 11, c(4,3) = 6, c(4,4) = 1 (sum = 24 = 4!)

6. **Row sum = n!:**
   Verify Σ_{k=0}^{n} c(n,k) = n! for n=0..6 via native_decide.

## Imports

```lean
import Mathlib.Tactic
```

## Constraints

- Must compile: `lake build AnalyticCombinatorics.PartA.Ch2.HarmonicNumbers`
- No sorry, no axiom
- Delete anything that doesn't compile
- native_decide for all checks
- Use ℚ for harmonic numbers (exact rational arithmetic)

## Output

Write file, verify build, report.
