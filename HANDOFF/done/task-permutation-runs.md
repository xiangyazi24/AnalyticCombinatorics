# Task: Permutation Runs and Descent Statistics (Ch III)

## Goal

Create `AnalyticCombinatorics/PartA/Ch3/PermutationRuns.lean`.

## What to formalize

A "run" in a permutation is a maximal ascending consecutive subsequence.
Number of runs = number of descents + 1. The Eulerian numbers A(n,k) count
permutations with k descents (already in MultivariateGF.lean). This file
adds complementary statistics.

1. **Number of permutations of [n] with exactly k ascents:**
   `ascentCount (n k : ℕ) : ℕ` — same as Eulerian A(n,k) since ascents = n-1-descents.
   Actually: number of descents + number of ascents = n - 1.
   So A(n,k) with k descents = A(n, n-1-k) with n-1-k ascents.
   
   Just verify the symmetry: descentCount n k = descentCount n (n-1-k).

2. **Peak numbers:**
   A peak at position i means σ(i-1) < σ(i) > σ(i+1).
   Number of permutations of [n] with exactly k peaks = P(n,k).
   
   P(3,0) = 2, P(3,1) = 4  (sum = 6 = 3!)
   P(4,0) = 2, P(4,1) = 16, P(4,2) = 6  ... wait let me recalculate.
   
   Actually peak counting is tricky. Simpler:

3. **Excedance numbers:**
   An excedance in σ is a position i where σ(i) > i.
   Number of permutations of [n] with exactly k excedances = Eulerian number A(n,k).
   (This is a well-known equidistribution result.)
   
   Define: `excedanceCount (n : ℕ) : ℕ := (Finset.range n.factorial).card`... too complex.
   
   Better: just verify that the total number of excedances across all permutations
   equals n! * (n-1) / 2 (same as inversions average).
   
   Actually: total excedances over all σ ∈ S_n = n! * (n-1) / 2.
   
   `totalExcedances (n : ℕ) : ℕ := n.factorial * (n - 1) / 2`
   Verify: n=2: 2*1/2=1, n=3: 6*2/2=6, n=4: 24*3/2=36

4. **Fixed points (derangement complement):**
   Number of permutations of [n] with exactly k fixed points:
   `fixedPointPerms (n k : ℕ) : ℕ := Nat.choose n k * subfactorial (n - k)`
   
   where subfactorial m = D_m (derangement count).
   
   Define subfactorial:
   ```lean
   def subfactorial : ℕ → ℕ
     | 0 => 1
     | 1 => 0
     | n + 2 => (n + 1) * (subfactorial (n + 1) + subfactorial n)
   ```
   
   Verify: D_0=1, D_1=0, D_2=1, D_3=2, D_4=9, D_5=44, D_6=265
   
   Verify fixedPointPerms: 
   - Σ_{k=0}^{n} fixedPointPerms n k = n! (for n=0..6)
   - fixedPointPerms n 0 = subfactorial n

5. **Mean number of fixed points = 1:**
   Total fixed points over all σ ∈ S_n = n! (each position contributes (n-1)! perms
   where it's fixed, times n positions = n * (n-1)! = n!).
   
   `totalFixedPoints (n : ℕ) : ℕ := n.factorial`
   
   Verify: Σ_{k=0}^{n} k * fixedPointPerms n k = n! for n=1..6.

## Imports

```lean
import Mathlib.Tactic
```

## Constraints

- Must compile: `lake build AnalyticCombinatorics.PartA.Ch3.PermutationRuns`
- No sorry, no axiom
- Delete anything that doesn't compile
- native_decide for all checks
- If a definition is hard to make terminating, switch to a simpler formulation
- Focus on subfactorial + fixed-point distribution as the main content

## Output

Write file, verify build, report.
